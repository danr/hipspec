module Halo.Lift(caseLetLift) where

import CoreFVs
import CoreUtils
import CoreSyn
import Id
import Name
import MkCore
import OccName
import Outputable
import Type
import UniqSupply
import Unique
import Var
import VarSet

import Halo.Util
import Halo.Shared

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative

-- | The lift environment, current function and its arguments
type LiftEnv = (Var,[Var])

args :: LiftEnv -> [Var]
args = snd

fun :: LiftEnv -> Var
fun = fst

-- | The initial environment
initEnv :: LiftEnv
initEnv = (error "initEnv: fun",[])

-- | The lift monad
type LiftM = WriterT [CoreBind] (ReaderT LiftEnv (WriterT [String] UniqSM))

-- | Write a debug message
dbgMsg :: String -> LiftM ()
dbgMsg = lift . tell . return

-- | Get a new unique identifier from the UniqSM
liftUnique :: LiftM Unique
liftUnique = lift . lift . lift $ getUniqueM

run :: LiftM a -> UniqSupply -> (((a,[CoreBind]),[String]),UniqSupply)
run m us = initUs us (runWriterT (runWriterT m `runReaderT` initEnv))

-- | caseLetLift a core program
caseLetLift :: [CoreBind] -> UniqSupply -> (([CoreBind],[String]),UniqSupply)
caseLetLift []     us = (([],[]),us)
caseLetLift (b:bs) us = ((mkCoreBind (flattenBinds (b':lifted_binds)):more_binds
                         ,msgs++more_msgs)
                        ,fin_us)
   where
     (((b',lifted_binds),msgs),us')  = run (liftCoreBind b) us
     ((more_binds,more_msgs),fin_us) = caseLetLift bs us'

-- | Lift a binding group
liftCoreBind :: CoreBind -> LiftM CoreBind
liftCoreBind b = case b of
    NonRec f e -> NonRec f <$> liftDecl f e
    Rec binds  -> Rec <$> sequence [ (,) f <$> liftDecl f e | (f,e) <- binds ]

-- | Translate a CoreDecl or a Let
liftDecl :: Var -> CoreExpr -> LiftM CoreExpr
liftDecl f e = do
    dbgMsg $ "Lifting " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
    dbgMsg $ "    rhs:" ++ showExpr e
    args_ <- asks args
    e_lifted <- local (const (f,args_++as)) (liftCase e_stripped)
    return (mkCoreLams (args_ ++ as) e_lifted)
  where
    (as,e_stripped) = collectBinders e

-- | Translate a case expression
liftCase :: CoreExpr -> LiftM CoreExpr
liftCase e = case e of
    Case scrutinee scrut_var ty alts -> do

        dbgMsg $ "Case on " ++ showExpr scrutinee

        lifted_scrutinee <- liftExpr scrutinee

        lifted_alts <- mapM liftAlt alts

        return $ Case lifted_scrutinee scrut_var ty lifted_alts

    _ -> liftExpr e

-- | Lift an alternative
liftAlt :: CoreAlt -> LiftM CoreAlt
liftAlt (con,bound,e) = do
    e_lifted <- local (second (++ bound)) (liftCase e)
    return (con,bound,e_lifted)

-- | Translate an expression, i.e. not case statements. Substitutions
-- are followed.
liftExpr :: CoreExpr -> LiftM CoreExpr
liftExpr e = case e of
    Var x          -> return (Var x)
    Lit i          -> return (Lit i)
    App e1 e2      -> App <$> liftExpr e1 <*> liftExpr e2
    Lam y e'       -> liftInnerLambda y e'
    Let bind in_e  -> liftInnerLet bind in_e
    Case s sv t as -> liftInnerCase s sv t as
    Cast e_cast c  -> Cast <$> liftExpr e_cast <*> pure c
    Tick t e_tick  -> Tick t <$> liftExpr e_tick
    Type t         -> return (Type t)
    Coercion c     -> return (Coercion c)
  where
    err s = error $ "liftExpr: " ++ s ++ " (" ++ showExpr e ++ ")"

mkLiftedName :: Type -> String -> LiftM Var
mkLiftedName ty lbl = do
    i <- liftUnique
    fun_var <- asks fun
    let fun_desc = showSDoc . ppr . localiseName . Var.varName $ fun_var
        name = mkSystemName i (mkOccName OccName.varName (fun_desc ++ "_" ++ lbl))
        var' = mkLocalId name ty
    return var'

-- | Lift inner lambda expression
liftInnerLambda :: Var -> CoreExpr -> LiftM CoreExpr
liftInnerLambda x e = do

    let fv_set   = exprFreeVars e

    lam_args <- filter (`elemVarSet` fv_set) <$> asks args

    let lam_args_x = lam_args ++ [x]

    new_fun <- mkLiftedName (mkPiTypes lam_args_x (exprType e)) "lam"

    dbgMsg $ "Lift lambda: " ++ showExpr (Lam x e) ++ " new name: " ++ show new_fun

    lifted_lam <- local (const (new_fun,lam_args_x))
                        (liftCoreBind (NonRec new_fun e))

    tell [lifted_lam]

    return $ mkVarApps (Var new_fun) lam_args

-- | Lift an inner case expression
liftInnerCase :: CoreExpr -> Var -> Type -> [CoreAlt] -> LiftM CoreExpr
liftInnerCase scrutinee scrut_var ty alts = do

    let e = Case scrutinee scrut_var ty alts

    arg_vars <- asks args

    let fv_set    = exprFreeVars e
        case_args = filter (`elemVarSet` fv_set) arg_vars

    new_fun <- mkLiftedName (mkPiTypes case_args ty) "case"

    dbgMsg $ "Lift case: " ++ showExpr e ++ " new name: " ++ show new_fun

    lifted_case <- local (const (new_fun,case_args))
                         (liftCoreBind (NonRec new_fun e))
    tell [lifted_case]

    return $ mkVarApps (Var new_fun) case_args

-- | Lift a let expression
liftInnerLet :: CoreBind -> CoreExpr -> LiftM CoreExpr
liftInnerLet b in_e = do
    dbgMsg $ "Experimental let: " ++ showExpr (Let b in_e)
    case b of
        NonRec v e -> do
            (lifted_bind,subst) <- liftInnerDecl v e

            tell [uncurry NonRec lifted_bind]

            liftExpr (substExprList in_e [subst])

        Rec binds -> do
            (lifted_binds,subst_list) <- mapAndUnzipM (uncurry liftInnerDecl) binds

            tell [Rec lifted_binds]

            liftExpr (substExprList in_e subst_list)

-- | Returns the substitution
liftInnerDecl :: Var -> CoreExpr -> LiftM ((Var,CoreExpr),(Var,CoreExpr))
liftInnerDecl v e = do

    arg_vars <- asks args

    let fv_set   = bindFreeVars (NonRec v e)
        let_args = filter (`elemVarSet` fv_set) arg_vars

    new_v <- mkLiftedName (mkPiTypes arg_vars (varType v))
                          (idToStr v ++ "let")

    let subst_v = mkVarApps (Var new_v) let_args

    lifted_e <- local (second (const let_args))
                      (liftDecl new_v (substExp e v subst_v))

    return ((new_v,lifted_e),(v,subst_v))


