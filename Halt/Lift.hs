module Halt.Lift where

import CoreFVs
import CoreSubst
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

import Halt.Names
import Halt.Util

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

-- | caseLetLift a core program
caseLetLift :: UniqSupply -> [CoreBind] -> ([CoreBind],[String])
caseLetLift us binds =

    let run :: LiftM a -> ((a,[CoreBind]),[String])
        run m = initUs_ us (runWriterT (runWriterT m `runReaderT` initEnv))

        juxtapose ((b,bs),msgs) = (reverse bs ++ [b],msgs)

        lifted_binds :: [[CoreBind]]
        msgss        :: [[String]]
        (lifted_binds,msgss) = unzip (map (juxtapose . run . liftCoreBind) binds)

     in (concat lifted_binds,concat msgss)

-- | Lift a binding group
liftCoreBind :: CoreBind -> LiftM CoreBind
liftCoreBind b = case b of
    NonRec f e -> NonRec f <$> liftDecl f e
    Rec binds  -> Rec <$> sequence [ (,) f <$> liftDecl f e | (f,e) <- binds ]

-- | Translate a CoreDecl or a Let
liftDecl :: Var -> CoreExpr -> LiftM CoreExpr
liftDecl f e = do
    dbgMsg $ "Lifting " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
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
    e_lifted <- local (second (++ bound)) (liftExpr e)
    return (con,bound,e_lifted)

-- | Translate an expression, i.e. not case statements. Substitutions
-- are followed.
liftExpr :: CoreExpr -> LiftM CoreExpr
liftExpr e = case e of
    Var x          -> return (Var x)
    Lit i          -> return (Lit i)
    App e1 e2      -> App <$> liftExpr e1 <*> liftExpr e2
    Lam _ _        -> err "lambdas should be lift before using liftLetCase"
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
        name = mkSystemName i (mkOccName OccName.varName (fun_desc ++ lbl))
        var' = mkLocalId name ty
    return var'

-- | Translate an inner case expression
liftInnerCase :: CoreExpr -> Var -> Type -> [CoreAlt] -> LiftM CoreExpr
liftInnerCase scrutinee scrut_var ty alts = do

    let e = Case scrutinee scrut_var ty alts

    dbgMsg $ "Lift case: " ++ showExpr e

    arg_vars <- asks args

    let fv_set    = exprFreeVars e
        case_args = filter (`elemVarSet` fv_set) arg_vars

    new_fun <- mkLiftedName (mkPiTypes case_args ty) "case"

    lifted_case <- local (const (new_fun,case_args))
                         (liftCoreBind (NonRec new_fun e))
    tell [lifted_case]

    return $ mkVarApps (Var new_fun) case_args

-- | Substitute everything in the list
substFromList :: [(Var,CoreExpr)] -> CoreExpr -> CoreExpr
substFromList = substExpr (text "subst") . extendIdSubstList emptySubst

-- | Translate a let expression
liftInnerLet :: CoreBind -> CoreExpr -> LiftM CoreExpr
liftInnerLet b in_e = do
    dbgMsg $ "Experimental let: " ++ showExpr (Let b in_e)
    case b of
        NonRec v e -> do
            (lifted_bind,subst) <- liftInnerDecl v e

            tell [uncurry NonRec lifted_bind]

            liftExpr (substFromList [subst] in_e)

        Rec binds -> do
            (lifted_binds,subst_list) <- mapAndUnzipM (uncurry liftInnerDecl) binds

            tell [Rec lifted_binds]

            liftExpr (substFromList subst_list in_e)

-- | Returns the substitution
liftInnerDecl :: Var -> CoreExpr -> LiftM ((Var,CoreExpr),(Var,CoreExpr))
liftInnerDecl v e = do

    arg_vars <- asks args

    let fv_set   = bindFreeVars (NonRec v e)
        let_args = filter (`elemVarSet` fv_set) arg_vars

    new_v <- mkLiftedName (mkPiTypes arg_vars (varType v))
                          (idToStr v ++ "let")

    let subst = (v,mkVarApps (Var new_v) let_args)

    lifted_e <- local (second (const let_args))
                      (liftDecl new_v (substFromList [subst] e))

    return ((new_v,lifted_e),subst)


