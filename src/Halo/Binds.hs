-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns, ExplicitForAll #-}
module Halo.Binds
    ( trBinds
    , BindPart(..), BindParts, BindMap, minRhs
    , trBindPart
    , trConstraints
    ) where

import CoreSubst
import CoreSyn
import PprCore
import DataCon
import Id
import Outputable

import Halo.Case
import Halo.Constraints
import Halo.ExprTrans
import Halo.FreeTyCons
import Halo.Monad
import Halo.Pointer
import Halo.Shared
import Halo.Subtheory
import Halo.Util

import Halo.FOL.Abstract

import Control.Monad.Reader
import Control.Monad.Error

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)
import Data.List

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it,
--   also returns the BindParts for every defined function
trBinds :: (Ord s,Show s) => [CoreBind] -> HaloM ([Subtheory s],BindMap s)
trBinds binds = do
    HaloEnv{..} <- ask

    let pointer_subthys = map (uncurry (mkPtr conf)) (M.toList arities)

    (fun_subthys,bind_maps) <- mapAndUnzipM (uncurry trBind) (flattenBinds binds)

    return (fun_subthys ++ pointer_subthys,M.unions bind_maps)

-- | We chop up a bind to several bind parts to be able to split
--   goals later to several invocations to theorem provers
data BindPart s = BindPart
    { bind_fun     :: Var
    , bind_args    :: [CoreExpr]
    , bind_rhs     :: Rhs
    , bind_constrs :: [Constraint]
    , bind_deps    :: [Content s]
    , bind_mins    :: [CoreExpr]
    -- ^ Unused when rhs = min
    }

-- | Many bind parts
type BindParts s = [BindPart s]

-- | A map from variables to bind parts
type BindMap s = Map Var (BindParts s)

-- | An rhs of a bind part
data Rhs
    = Min { rhsExpr :: CoreExpr }
    | Rhs { rhsExpr :: CoreExpr }

minRhs :: Rhs -> Bool
minRhs Min{} = True
minRhs _     = False

-- | Make a bind part given the rhs, with a given min set
bindPart :: Ord s => Rhs -> HaloM (BindPart s)
bindPart rhs = do
    HaloEnv{current_fun,args,constr,min_set} <- ask
    let bind_part = BindPart
            { bind_fun     = current_fun
            , bind_args    = args
            , bind_rhs     = rhs
            , bind_constrs = constr
            , bind_mins    = min_set
            , bind_deps    = bindPartDeps bind_part
            }
    return bind_part

-- | Translate a bind part to formulae. Does not capture used pointers,
--   doesn't look at min set of binds.
trBindPart :: BindPart s -> HaloM Formula'
trBindPart BindPart{..} = do
    tr_constr <- trConstraints bind_constrs
    lhs <- apply bind_fun <$> mapM trExpr bind_args
    consequent <- case bind_rhs of
               Min scrut -> min' <$> trExpr scrut
               Rhs rhs   -> (lhs ===) <$> trExpr rhs
    return $ foralls (min' lhs : tr_constr ===> consequent)

-- | Make a subtheory for bind parts that regard the same function
trBindParts :: Ord s => Var -> CoreExpr -> BindParts s -> HaloM (Subtheory s)
trBindParts f e parts = do

    -- Capturing of pointers when translating all expressions in the bind parts
    (tr_formulae,used_ptrs) <- capturePtrs (mapM trBindPart parts)

    -- We could get this information from the bind_deps, but this is more efficient
    let deps = map Function (delete f (exprFVs e))
            ++ map Data (freeTyCons e)
            ++ map Pointer used_ptrs

    return $ Subtheory
        { provides    = Function f
        , depends     = deps
        , description = idToStr f ++ " = " ++ showSDoc (pprCoreExpr e)
                     ++ "\nDependencies: " ++ unwords (map baseContentShow deps)
        , formulae    = tr_formulae
        }

-- | Translate a Var / CoreExpr pair flattened from a CoreBind
trBind :: (Ord s,Show s) => Var -> CoreExpr -> HaloM (Subtheory s,BindMap s)
trBind f e = err_handler $ do
    bind_parts <- trDecl f e
    subthy <- trBindParts f e bind_parts
    return (subthy,M.singleton f bind_parts)
  where
    err_handler m = m `catchError` \err -> do
      cleanUpFailedCapture
      return ((mkDummySubtheory (Function f))
              { formulae = error $ "trBind, " ++ show f ++ " yielded " ++ err }
             ,M.empty)

-- | Translate a CoreDecl to bind parts
trDecl :: Ord s => Var -> CoreExpr -> HaloM (BindParts s)
trDecl f e = do
    let as :: [Var]
        e' :: CoreExpr
        (_ty,as,e') = collectTyAndValBinders e

        new_env env = env
            { current_fun = f
            , args        = map Var as
            }

    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)

    bind_parts <- local new_env (trCase e')

    -- Remove the conflicting bind parts
    return $ filter (not . conflict . bind_constrs) bind_parts

-- | Translate a case expression
trCase :: Ord s => CoreExpr -> HaloM (BindParts s)
trCase (Case scrutinee scrut_var _ty alts_unsubst) = do

    write $ "Case on " ++ showExpr scrutinee

    -- Substitute the scrutinee var to the scrutinee expression
    let subst_alt (c,bs,e_alt) = (c,bs,substExp e_alt scrut_var scrutinee)

        alts_wo_bottom = map subst_alt alts_unsubst

    -- The min part, makes the scrutinee interesting
    min_part <- bindPart (Min scrutinee)

    -- Add a bottom case
    alts' <- addBottomCase alts_wo_bottom

    -- Everything happens under this scrutinee
    local (extendMinSet scrutinee) $ do

         -- If there is a default case, translate it separately
         (alts,def_part) <- case alts' of

              (DEFAULT,[],def_expr):alts -> do

                  -- Collect the negative patterns
                  neg_constrs <- mapM (invertAlt scrutinee) alts

                  -- Translate the default formula which happens on the negative
                  -- constraints
                  def_part' <- local (\env -> env { constr = neg_constrs ++ constr env })
                                        (trCase def_expr)

                  return (alts,def_part')

              alts -> return (alts,[])

         -- Translate the alternatives that are not deafult
         -- (mutually recursive with this function)
         alt_parts <- concatMapM (trAlt scrutinee) alts

         return (min_part : alt_parts ++ def_part)

trCase e = return <$> bindPart (Rhs e)

-- | Make a constraint from a case alternative
invertAlt :: CoreExpr -> CoreAlt -> HaloM Constraint
invertAlt scrut_exp (cons,_,_) = case cons of
    DataAlt data_con -> return (Inequality scrut_exp data_con)
    DEFAULT -> throwError "invertAlt: on DEFAULT, internal error"
    _       -> throwError "invertAlt: on LitAlt, literals not supported (yet)"

-- | Translate a case alternative
trAlt :: Ord s => CoreExpr -> CoreAlt -> HaloM (BindParts s)
trAlt scrut_exp alt@(cons,_,_) = case cons of
    DataAlt data_con -> trCon data_con scrut_exp alt
    DEFAULT -> throwError "trAlt: on DEFAULT, internal error"
    _       -> throwError "trAlt: on LitAlt, literals not supported (yet)"

-- | Translate a data con alternative from a case
trCon :: Ord s => DataCon -> CoreExpr -> CoreAlt -> HaloM (BindParts s)
trCon data_con scrut_exp (_cons,bound,e) = do
    HaloEnv{arities} <- ask
    let isQuant x = x `M.notMember` arities
    case scrut_exp of
        Var x | isQuant x -> do
            let tr_pat = foldApps (Var (dataConWorkId data_con)) (map Var bound)
                s = extendIdSubst emptySubst x (tr_pat)
                e' = substExpr (text "trAlt") s e
            local (substContext s) (trCase e')
        _ -> local (pushConstraint . Equality scrut_exp data_con . map Var $ bound)
                   (trCase e)

-- | Translate and nub constraints
trConstraints :: [Constraint] -> HaloM [Formula']
trConstraints constrs = do
    let write_cs hdr cs = write $ hdr ++ concatMap ("\n    " ++) (map show cs)
    write_cs "Constraints: " constrs
    if conflict constrs
        then throwError "  Conflict!"
        else do
            let not_redundant = rmRedundantConstraints constrs
            write_cs "Not redundant: " not_redundant
            mapM trConstr not_redundant

-- | Translate one constraint
trConstr :: Constraint -> HaloM Formula'
trConstr (Equality e data_con bs) = do
    lhs <- trExpr e
    rhs <- apply (dataConWorkId data_con) <$> mapM trExpr bs
    return $ lhs === rhs
trConstr (Inequality e data_con) = do
    lhs <- trExpr e
    let rhs = apply (dataConWorkId data_con)
                    [ proj i (dataConWorkId data_con) lhs
                    | i <- [0..dataConSourceArity data_con-1] ]
    return $ lhs =/= rhs

-- | Non-pointer dependencies of an expression
exprDeps :: Ord s => CoreExpr -> Set (Content s)
exprDeps = S.fromList
         . ((++) <$> (map Function . exprFVs) <*> (map Data . freeTyCons))

-- | Non-pointer dependencies of a constraint
constraintDeps :: Ord s => Constraint -> Set (Content s)
constraintDeps c = case c of
    Equality e dc _es -> S.insert (dcContent dc) (exprDeps e)
    Inequality e dc   -> S.insert (dcContent dc) (exprDeps e)
  where
    dcContent :: DataCon -> Content s
    dcContent = Data . dataConTyCon

-- | Calculates the non-pointer dependencies of a bind part
bindPartDeps :: Ord s => BindPart s -> [Content s]
bindPartDeps BindPart{..}
    = S.toList $ S.delete (Function bind_fun) (free S.\\ bound)
  where
    free = S.unions $ [ args_dcs, exprDeps (rhsExpr bind_rhs) ]
                   ++ map exprDeps bind_mins
                   ++ map constraintDeps bind_constrs

    bound = args_bound `S.union` constr_bound

    -- Don't regard arguments as a dependency
    (args_bound,args_dcs) = S.partition isFunction (S.unions (map exprDeps bind_args))

    -- Variables bound in constraints from casing on non-var scrutinees
    constr_bound = S.unions (map constr_bind bind_constrs)
      where
        constr_bind (Equality _ _ es) = S.unions (map exprDeps es)
        constr_bind _                 = S.empty

    isFunction Function{} = True
    isFunction _          = False

