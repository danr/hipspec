-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
module Halo.Binds ( trBinds ) where

import CoreSubst
import CoreSyn
import CoreFVs
import UniqSet
import PprCore
import DataCon
import Id
import Outputable

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

import Halo.FOL.Abstract

import Control.Monad.Reader
import Control.Monad.Error

import Data.Map (toList,notMember)

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
trBinds :: [CoreBind] -> HaloM [Subtheory s]
trBinds binds = do
    HaloEnv{..} <- ask

    let tr_pointers = map (uncurry (mkPtr conf)) (toList arities)

    tr_funs <- concatMapM trBind binds

    return (tr_funs ++ tr_pointers)

-- | Translate a group of mutally defined binders
trBind :: CoreBind -> HaloM [Subtheory s]
trBind bind = mapM (uncurry trDecl) (flattenBinds [bind])

-- | Translate a CoreDecl, given the mutual group it was defined in
--
--   Generates a small subtheory for it including its pointer axiom
trDecl :: Var -> CoreExpr -> HaloM (Subtheory s)
trDecl f e = do

    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)

    let fun_deps = uniqSetToList (exprFreeIds e `delOneFromUniqSet` f)

        data_deps = freeTyCons e

        tr_e = (`local` trCase e') $ \env -> env
                    { current_fun = f, args = map Var as ++ args env }

    (fun_tr,used_ptrs) <- capturePtrs tr_e `catchError` \err -> do
                              cleanUpFailedCapture
                              return (error err,[])

    return $ Subtheory
        { provides    = Function f
        , depends     = map Function fun_deps
                     ++ map Pointer used_ptrs
                     ++ map Data data_deps
        , description = idToStr f ++ " = " ++ showSDoc (pprCoreExpr e)
                        ++ "\nDependencies: "
                        ++ unwords (map idToStr fun_deps)
        , formulae    = fun_tr
        }
  where
    -- Collect the arguments and the body expression
    as :: [Var]
    e' :: CoreExpr
    (_ty,as,e') = collectTyAndValBinders e

-- | Translate a case expression
trCase :: CoreExpr -> HaloM [Formula']
trCase (Case scrutinee scrut_var _ty alts_unsubst) = do

    write $ "Case on " ++ showExpr scrutinee

    -- Substitute the scrutinee var to the scrutinee expression
    let subst_alt (c,bs,e_alt) = (c,bs,substExp e_alt scrut_var scrutinee)

        alts_wo_bottom = map subst_alt alts_unsubst

    HaloConf{..} <- asks conf

    min_formula <- do
        m_tr_constr <- trConstraints
        case m_tr_constr of
            Nothing -> return []
            Just tr_constr -> do
                lhs <- trLhs
                tr_scrut <- trExpr scrutinee
                let constr = min' lhs : tr_constr
                return [foralls $ constr ===> min' tr_scrut]

    -- Add a bottom case
    alts' <- addBottomCase alts_wo_bottom

    -- If there is a default case, translate it separately
    (alts,def_formula) <- case alts' of

         (DEFAULT,[],def_expr):alts -> do

             -- Collect the negative patterns
             neg_constrs <- mapM (invertAlt scrutinee) alts

             -- Translate the default formula which happens on the negative
             -- constraints
             def_formula' <- local (\env -> env { constr = neg_constrs ++ constr env })
                                   (trCase def_expr)

             return (alts,def_formula')

         alts -> return (alts,[])

    -- Translate the alternatives that are not deafult
    -- (mutually recursive with this function)
    alt_formulae <- concatMapM (trAlt scrutinee) alts

    return (min_formula ++ alt_formulae ++ def_formula)

trCase e = do

    HaloEnv{current_fun} <- ask
    write $ "At the end of " ++ idToStr current_fun ++ "'s branch: " ++ showExpr e
    m_tr_constr <- trConstraints
    case m_tr_constr of
        Nothing -> return []
        Just tr_constr -> do
            lhs <- trLhs
            rhs <- trExpr e
            return [foralls $ min' lhs : tr_constr ===> lhs === rhs]

trLhs :: HaloM Term'
trLhs = do
    HaloEnv{current_fun,args} <- ask
    apply current_fun <$> mapM trExpr args

invertAlt :: CoreExpr -> CoreAlt -> HaloM Constraint
invertAlt scrut_exp (cons,_,_) = case cons of
    DataAlt data_con -> return (Inequality scrut_exp data_con)
    DEFAULT -> throwError "invertAlt: on DEFAULT, internal error"
    _       -> throwError "invertAlt: on LitAlt, literals not supported (yet)"

trAlt :: CoreExpr -> CoreAlt -> HaloM [Formula']
trAlt scrut_exp alt@(cons,_,_) = case cons of
    DataAlt data_con -> trCon data_con scrut_exp alt
    DEFAULT -> throwError "trAlt: on DEFAULT, internal error"
    _       -> throwError "trAlt: on LitAlt, literals not supported (yet)"

trCon :: DataCon -> CoreExpr -> CoreAlt -> HaloM [Formula']
trCon data_con scrut_exp (_cons,bound,e) = do
    HaloEnv{arities} <- ask
    let isQuant x = x `notMember` arities
    case scrut_exp of
        Var x | isQuant x -> do
            let tr_pat = foldApps (Var (dataConWorkId data_con)) (map Var bound)
                s = extendIdSubst emptySubst x (tr_pat)
                e' = substExpr (text "trAlt") s e
            local (substContext s) (trCase e')
        _ -> local (pushConstraint . Equality scrut_exp data_con . map Var $ bound)
                   (trCase e)

trConstraints :: HaloM (Maybe [Formula'])
trConstraints = do
    HaloEnv{constr} <- ask
    let write_cs hdr cs = write $ hdr ++ concatMap ("\n    " ++) (map show cs)
    write_cs "Constraints: " constr
    if conflict constr
        then write "  Conflict!" >> return Nothing
        else do
            let not_redundant = rmRedundantConstraints constr
            write_cs "Not redundant: " not_redundant
            Just <$> mapM trConstr not_redundant

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
