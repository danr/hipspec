{-# LANGUAGE
        ExplicitForAll,
        NamedFieldPuns,
        ParallelListComp,
        PatternGuards,
        RecordWildCards
  #-}
{-

    Translating Core Binds, i.e. function definitions

    When casing on a scrutinee, you either:

        * substitute the patterns (when casing on a variable)

        * generate a constraint (see Halo.Constraint)

    To be able to split the definitions into several theorem prover
    invocations, we also generate `BindParts', that are translated to a
    single subtheory for each binder, see `trBind'. The example where
    BindParts is used elsewhere is in the contracts checker in
    Contracts.Trans.trSplit.

-}
module Halo.Binds (trBind, trBinds) where

import CoreSubst
import CoreSyn
import DataCon
import Id
import Literal
import Outputable

import Var
import TysPrim
import Type

import Halo.Case
import Halo.Conf
import Halo.Constraints
import Halo.ExprTrans
import Halo.FreeTyCons
import Halo.Monad
import Halo.Pointer
import Halo.Shared
import Halo.Subtheory
import Halo.Util
import Halo.MonoType

import Halo.FOL.Abstract

import Control.Monad.Reader
import Control.Monad.Error

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)
import Data.List

import Data.Void

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it,
--   also returns the BindParts for every defined function
trBinds :: [CoreBind] -> HaloM [Subtheory Void]
trBinds = concatMapM trBind

-- | Translates the function(s) and the pointer axiom(s)
trBind :: CoreBind -> HaloM [Subtheory Void]
trBind bind = catch_err $ do

    let vses = flattenBinds [bind]

    (fun_subthys,_bind_maps) <- mapAndUnzipM (uncurry trVarCoreExpr) vses

    pointer_subthys <- mapM (mkPtr . fst) vses

    return (fun_subthys ++ pointer_subthys)
  where
    catch_err m = m `catchError` \ w -> write w >> return []

-- | We chop up a bind to several bind parts to be able to split
--   goals later to several invocations to theorem provers
--   (currently unused)
data BindPart = BindPart
    { bind_fun     :: Var
    , bind_args    :: [CoreExpr]
    , bind_rhs     :: Either CoreExpr Term'
    , bind_qvars   :: [Var]
    , bind_constrs :: [Constraint]
    , bind_deps    :: [Content Void]
    }

-- | Many bind parts
type BindParts = [BindPart]

-- | A map from variables to bind parts
type BindMap = Map Var BindParts

bindPartEither :: Either CoreExpr Term' -> HaloM BindPart
bindPartEither rhs = do
    HaloEnv{current_fun,args,constr,qvars} <- ask
    let bind_part = BindPart
            { bind_fun     = current_fun
            , bind_args    = args
            , bind_qvars   = S.toList qvars
            , bind_rhs     = rhs
            , bind_constrs = constr
            , bind_deps    = bindPartDeps bind_part
            }
    return bind_part

bindPart :: CoreExpr -> HaloM BindPart
bindPart = bindPartEither . Left

bindPartTerm :: Term' -> HaloM BindPart
bindPartTerm = bindPartEither . Right

-- | Translate a bind part to formulae. Does not capture used pointers,
--   doesn't look at min set of binds.
trBindPart :: BindPart -> HaloM Formula'
trBindPart BindPart{..} = local (addQuantVars bind_qvars) $ do
    tr_constr <- trConstraints bind_constrs
    lhs <- apply bind_fun <$> mapM trExpr bind_args
    rhs <- case bind_rhs of
        Left rhs_expr -> trExpr rhs_expr
        Right rhs_tm  -> return rhs_tm
    foralls varMonoType (tr_constr ===> lhs === rhs)

-- | Make a subtheory for bind parts that regard the same function
trBindParts :: Var -> CoreExpr -> BindParts -> HaloM (Subtheory Void)
trBindParts f e parts = do

    formulae <- mapM trBindPart parts

    -- We get this information from the bind_deps, in case
    -- we filter away a branch with conflicting constraints
    let deps = nub $ concatMap bind_deps parts

    monotype <- varMonoType f

    return $ calculateDeps subtheory
        { provides = Function f
        , depends  = deps
        , clauses  =
            comment (showOutputable f ++ " = " ++ showOutputable e) :
            typeSig' (AFun f) monotype :
            definitions formulae
        }

-- | Translate a Var / CoreExpr pair flattened from a CoreBind
trVarCoreExpr :: Var -> CoreExpr -> HaloM (Subtheory Void,BindMap)
trVarCoreExpr f e = do
    bind_parts <- trDecl f e
    subthy <- trBindParts f e bind_parts
    return (subthy,M.singleton f bind_parts)

-- | Translate a CoreDecl to bind parts
trDecl :: Var -> CoreExpr -> HaloM BindParts
trDecl f e = do
    let as :: [Var]
        e' :: CoreExpr
        (as,e') = collectValBinders e

        new_env env = env
            { current_fun = f
            , args        = map Var as
            }

    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)

    bind_parts <- local (new_env . addQuantVars as) (trCase e')

    let hasConflict bp
            | conflict (bind_constrs bp) = do
                write ("Conflict : " ++ show (bind_constrs bp))
                return False
            | otherwise                  = return True

    -- Remove the conflicting bind parts
    filterM hasConflict bind_parts

-- | Translate a case expression
trCase :: CoreExpr -> HaloM BindParts
trCase e@(Case scrutinee scrut_var ty alts_unsubst)

    -- First, check if we are casing on a constructor already!
    | Just rhs <- tryCase scrutinee scrut_var alts_unsubst = do

        write $ "This is a case on a constructor: " ++ showExpr e
        write $ "Continuing with right hand side: " ++ showExpr rhs
        trCase rhs

    -- First, check if we are casing on a constructor already!
    | [(DEFAULT,[],rhs)] <- alts_unsubst = do

        write $ "This is a case with only a DEFAULT: " ++ showExpr e
        write $ "Continuing with right hand side: " ++ showExpr rhs
        let rhs' = substExp scrut_var scrutinee rhs
        write $ "Substituted with scrut var: " ++ showExpr rhs'
        trCase rhs'

    | otherwise = do

        write $ "Case on " ++ showExpr scrutinee

        -- Substitute the scrutinee var to the scrutinee expression
        let subst_alt (c,bs,e_alt) = (c,bs,substExp scrut_var scrutinee e_alt)

            alts_wo_bottom = map subst_alt alts_unsubst

            primitive_case = varType scrut_var `eqType` intPrimTy

        write $ "Adding bottom case, scrut var type is " ++
            showOutputable (varType scrut_var) ++
            " primive_case: " ++ show primitive_case

        -- Add UNR/BAD alternatives, unless casing on a primitive (say Int#)
        alts' <- if primitive_case
                    then do
                        write "No bottom case on primitive int"
                        return (mkLefts alts_wo_bottom)
                    else addBottomCase ty alts_wo_bottom


        -- If there is a default case, translate it separately
        (alts,def_part) <- case alts' of

            (DEFAULT,[],def):alts -> do

                -- Collect the negative patterns
                neg_constrs <- mapM (invertAlt scrutinee) (rmLefts alts)

                -- Translate the default formula which happens
                -- on the negative constraints
                let mod_env env = env { constr = neg_constrs ++ constr env }
                def_part' <- local mod_env $ case def of
                                Left def_expr -> trCase def_expr
                                Right def_term -> return <$> bindPartTerm def_term

                return (alts,def_part')

            alts -> return (alts,[])

        -- Translate the alternatives that are not deafult
        -- (mutually recursive with this function)
        alt_parts <- concatMapM (trAlt scrutinee) (rmLefts alts)

        return (alt_parts ++ def_part)

trCase e = return <$> bindPart e

-- | If this case cases on a constructor already, pick the right alternative!
tryCase :: CoreExpr -> Var -> [CoreAlt] -> Maybe CoreExpr
tryCase scrut scrut_var alts = case collectArgs scrut of
    (Var c,es)
        | Just dc <- isDataConId_maybe c -> case alts of
            _ | Just (_,bs,rhs) <- find_alt dc alts -> do
                     guard (length bs == length es)
                     let rhs' = (substExprList (zip bs es) rhs)
                     return (substExp scrut_var scrut rhs')
            (DEFAULT,[],rhs):_ -> return rhs
            _                  -> Nothing
    _ -> Nothing
  where
    find_alt :: DataCon -> [CoreAlt] -> Maybe CoreAlt
    find_alt dc (alt:alts') = case alt of
        (DataAlt dc',_,_) | dc == dc' -> Just alt
        _                             -> find_alt dc alts'
    find_alt _ [] = Nothing

-- | Make an inequality constraint from a case alternative, when handling
--   the DEFAULT case. A constructor like Cons gets a constraint that
--   looks like x /= Cons(sel_0_Cons(x),sel_1_Cons(x))
--   (projections are added in trConstraints)
invertAlt :: CoreExpr -> CoreAlt -> HaloM Constraint
invertAlt scrut_exp (cons,_,_) = case cons of
    DataAlt data_con        -> return (Inequality scrut_exp data_con)
    LitAlt (MachInt i)      -> return (LitInequality scrut_exp i)
    LitAlt (LitInteger i _) -> return (LitInequality scrut_exp i)
    LitAlt _ -> throwError "invertAlt: on non-integer alternative"
    DEFAULT  -> throwError "invertAlt: on DEFAULT, internal error"

-- | Translate a case alternative
trAlt :: CoreExpr -> CoreAlt -> HaloM BindParts
trAlt scrut_exp (cons,bound,e) = do

    (subst_expr,equality_constraint) <- case cons of
        DataAlt data_con -> return
            (foldApps (Var (dataConWorkId data_con)) (map Var bound)
            ,Equality scrut_exp data_con (map Var bound))
        LitAlt lit@(MachInt i) -> return
            (Lit lit,LitEquality scrut_exp i)
        LitAlt lit@(LitInteger i _) -> return
            (Lit lit,LitEquality scrut_exp i)
        LitAlt _ -> throwError "trAlt: on non-integer alternative"
        DEFAULT  -> throwError "trAlt: on DEFAULT, internal error"

    HaloEnv{qvars,conf = HaloConf{var_scrut_constr}} <- ask
    let isQuant x = x `S.member` qvars

    case removeCruft scrut_exp of
        Var x | isQuant x && not var_scrut_constr -> do
            let s = extendIdSubst emptySubst x subst_expr
                e' = substExpr (text "trAlt") s e
            local (substContext s . addQuantVars bound) (trCase e')
        _ -> local (pushConstraint equality_constraint . addQuantVars bound) (trCase e)

-- | Translate and nub constraints
trConstraints :: [Constraint] -> HaloM [Formula']
trConstraints constrs = do
    let write_cs hdr cs = write $ hdr ++ show cs
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
trConstr (LitEquality e i)   = (litInteger i ===) <$> trExpr e
trConstr (LitInequality e i) = (litInteger i =/=) <$> trExpr e

-- | Non-pointer dependencies of an expression
exprDeps :: CoreExpr -> Set (Content Void)
exprDeps = S.fromList
         . ((++) <$> (map Function . exprFVs) <*> (map Data . freeTyCons))

-- | Non-pointer dependencies of a constraint
constraintDeps :: Constraint -> Set (Content Void)
constraintDeps c = case c of
    Equality e dc _es    -> S.insert (dcContent dc) (exprDeps e)
    Inequality e dc      -> S.insert (dcContent dc) (exprDeps e)
    LitEquality e _      -> exprDeps e
    LitInequality e _    -> exprDeps e
  where
    dcContent :: DataCon -> Content s
    dcContent = Data . dataConTyCon

-- | Calculates the non-pointer dependencies of a bind part
bindPartDeps :: BindPart -> [Content Void]
bindPartDeps BindPart{..}
    = S.toList $ S.delete (Function bind_fun) (free S.\\ bound)
  where
    free = S.unions $ [ args_dcs
                      , case bind_rhs of
                            Left expr -> exprDeps expr
                            Right _   -> S.empty
                      ]
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

