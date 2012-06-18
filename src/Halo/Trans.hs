-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
module Halo.Trans(translate) where

import CoreSubst
import CoreSyn
import CoreFVs
import UniqSet
import PprCore
import DataCon
import Id
import Outputable
import TyCon

import Halo.Util
import Halo.Shared
import Halo.Monad
import Halo.Conf
import Halo.Data
import Halo.ExprTrans
import Halo.Constraints
import Halo.Case
import Halo.Subtheory

import Halo.FOL.Abstract

import Control.Monad.Reader

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
--   TODO: Register used function pointers
translate :: HaloEnv -> [TyCon] -> [CoreBind] -> ([Subtheory],[String])
translate env ty_cons binds =
  let tr_funs :: [Subtheory]
      msgs :: [String]
      (tr_funs,msgs) = runHaloM env (mapM trBind binds)

  in  (concat
          [mkProjDiscrim (conf env) ty_cons
          ,mkCF          (conf env) ty_cons
          ,axiomsBadUNR  (conf env)
          {- ,pointers -}
          ,tr_funs]
      ,msgs ++ showArityMap (arities env))


trBind :: CoreBind -> HaloM Subtheory
trBind bind = do
    let fses       = flattenBinds [bind]
        fun_names  = map fst fses

    fun_translated <- concatMapM (uncurry trDecl) fses

    let dependencies = uniqSetToList (bindFreeVars bind)

    return $ Subtheory { provides    = Function fun_names
                       , depends     = map (Function . (:[])) dependencies
                       , description = showSDoc (pprCoreBinding bind)
                                     ++ "\nDependencies: "
                                     ++ unwords (map idToStr dependencies)
                       , formulae    = fun_translated
                       }

-- | Translate a CoreDecl
trDecl :: Var -> CoreExpr -> HaloM [Formula']
trDecl f e = do
    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
    local (\env -> env { current_fun = f
                       , args = map Var as ++ args env
                       , quant = as ++ quant env}) (trCase e')
  where
    -- Collect the arguments and the body expression
    as :: [Var]
    e' :: CoreExpr
    (_ty,as,e') = collectTyAndValBinders e

-- | Translate a case expression
trCase :: CoreExpr -> HaloM [Formula']
trCase e = case e of
    Case scrutinee scrut_var _ty alts_unsubst -> do

        write $ "Case on " ++ showExpr scrutinee

        -- Substitute the scrutinee var to the scrutinee expression
        let subst_alt (c,bs,e_alt) = (c,bs,substExpr (text "trCase") s e_alt)
              where  s = extendIdSubst emptySubst scrut_var scrutinee

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
                    qvars <- asks quant
                    return [ forall' qvars $ constr ===> min' tr_scrut | use_min ]

        -- Add a bottom case
        alts' <- addBottomCase alts_wo_bottom

        -- If there is a default case, translate it separately
        (alts,def_formula) <- case alts' of

             (DEFAULT,[],def_expr):alts -> do

                 -- Collect the negative patterns
                 let neg_constrs = map (invertAlt scrutinee) alts

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
    _ -> do
        HaloEnv{current_fun,quant} <- ask
        HaloConf{..} <- asks conf
        write $ "At the end of " ++ idToStr current_fun ++ "'s branch: " ++ showExpr e
        m_tr_constr <- trConstraints
        case m_tr_constr of
            Nothing -> return []
            Just tr_constr -> do
                lhs <- trLhs
                rhs <- trExpr e
                return [forall' quant $
                          [ min' lhs | use_min ] ++ tr_constr ===> lhs === rhs]


trLhs :: HaloM Term'
trLhs = do
    HaloEnv{current_fun,args} <- ask
    apply current_fun <$> mapM trExpr args


invertAlt :: CoreExpr -> CoreAlt -> Constraint
invertAlt scrut_exp (cons, _bs, _) = case cons of
    DataAlt data_con -> Inequality scrut_exp data_con
    DEFAULT          -> error "invertAlt on DEFAULT"
    _                -> error "invertAlt on LitAlt (literals not supported yet!)"


trAlt :: CoreExpr -> CoreAlt -> HaloM [Formula']
trAlt scrut_exp (cons, bound, e) = do
    HaloEnv{quant} <- ask

    case cons of
        DataAlt data_con -> do
            case scrut_exp of
                Var x | x `elem` quant -> do
                    let tr_pat = foldl App (Var (dataConWorkId data_con)) (map Var bound)
                        s = extendIdSubst emptySubst x (tr_pat)
                        e' = substExpr (text "trAlt") s e
                    local (substContext s . pushQuant bound . delQuant x) (trCase e')
                _ -> local (pushConstraint (Equality scrut_exp data_con (map Var bound))
                           . pushQuant bound)
                           (trCase e)

        DEFAULT -> error "trAlt on DEFAULT"
        _       -> error "trAlt on LitAlt (literals not supported yet!)"

trConstraints :: HaloM (Maybe [Formula'])
trConstraints = do
    HaloEnv{constr} <- ask
    write $ "Constraints: " ++ concatMap ("\n    " ++) (map show constr)
    if conflict constr
        then write "  Conflict!" >> return Nothing
        else Just <$> mapM trConstr constr

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

