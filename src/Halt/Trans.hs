-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
module Halt.Trans(translate) where

import CoreSubst
import CoreSyn
import DataCon
import Id
import Outputable
import TyCon

import Halt.Common
import Halt.Utils
import Halt.Monad
import Halt.Conf
import Halt.Data
import Halt.ExprTrans
import Halt.Constraints
import Halt.Case

import Halt.FOL.Abstract

import Control.Monad.Reader

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
--   TODO: Register used function pointers
translate :: HaltEnv -> [TyCon] -> [CoreBind] -> ([AxClause],[VarClause],[String])
translate env ty_cons program =
  let -- Remove the unnecessary SCC information
      binds :: [(Var,CoreExpr)]
      binds = flattenBinds program

      -- Translate each declaration
      -- TODO : Make these return Decl?
      translated :: HaltM [VarFormula]
      translated = concatMapM (uncurry trDecl) binds

      formulae :: [VarFormula]
      msgs :: [String]
      (formulae,msgs) = runHaltM env translated

  in  (concat [mkProjs (conf env) ty_cons
              ,mkDiscrim (conf env) ty_cons
              ,mkCF (conf env) ty_cons
              ,axiomsBadUNR (conf env)]
      ,[ Clause Definition (show n) phi
       | phi <- formulae
       | n <- [(0 :: Int)..]]
      ,msgs ++ showArityMap (arities env))

-- | Translate a CoreDecl or a Let
trDecl :: Var -> CoreExpr -> HaltM [VarFormula]
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
trCase :: CoreExpr -> HaltM [VarFormula]
trCase e = case e of
    Case scrutinee scrut_var _ty alts_unsubst -> do

        write $ "Case on " ++ showExpr scrutinee

        -- Substitute the scrutinee var to the scrutinee expression
        let subst_alt (c,bs,e) = (c,bs,substExpr (text "trCase") s e)
              where  s = extendIdSubst emptySubst scrut_var scrutinee

            alts_wo_bottom = map subst_alt alts_unsubst

        HaltConf{..} <- asks conf

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
        HaltEnv{current_fun,quant} <- ask
        HaltConf{..} <- asks conf
        write $ "At the end of " ++ idToStr current_fun ++ "'s branch: " ++ showExpr e
        m_tr_constr <- trConstraints
        case m_tr_constr of
            Nothing -> return []
            Just tr_constr -> do
                lhs <- trLhs
                rhs <- trExpr e
                return [forall' quant $
                          [ min' lhs | use_min ] ++ tr_constr ===> lhs === rhs]


trLhs :: HaltM VarTerm
trLhs = do
    HaltEnv{current_fun,args} <- ask
    apply current_fun <$> mapM trExpr args


invertAlt :: CoreExpr -> CoreAlt -> Constraint
invertAlt scrut_exp (cons, _bs, _) = case cons of
    DataAlt data_con -> Inequality scrut_exp data_con
    DEFAULT          -> error "invertAlt on DEFAULT"
    _                -> error "invertAlt on LitAlt (literals not supported yet!)"


trAlt :: CoreExpr -> CoreAlt -> HaltM [VarFormula]
trAlt scrut_exp (cons, bound, e) = do
    HaltEnv{quant} <- ask

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

trConstraints :: HaltM (Maybe [VarFormula])
trConstraints = do
    HaltEnv{constr} <- ask
    write $ "Constraints: " ++ concatMap ("\n    " ++) (map show constr)
    if conflict constr
        then write "  Conflict!" >> return Nothing
        else Just <$> mapM trConstr constr

trConstr :: Constraint -> HaltM VarFormula
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

