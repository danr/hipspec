module Halt.Lift where

import PprCore
import CoreSyn
import CoreSubst
import CoreUtils
import CoreFVs
import Outputable
import Var
import VarEnv
import VarSet

import Debug.Trace

import Halt.Util

import Control.Monad.Writer
import Control.Monad.Reader

write :: CoreBind -> LiftM ()
write x = tell [x]

type LiftM = ReaderT [CoreBndr] (Writer [CoreBind])

liftProgram :: [CoreBind] -> [CoreBind]
liftProgram = execWriter . (`runReaderT` []) . mapM_ liftBndr

liftBndr :: CoreBind -> LiftM ()
liftBndr (NonRec b e) = write . NonRec b =<< liftLambda b e
liftBndr (Rec bses)   = write . Rec =<< sequence [ (,) b <$> liftLambda b e
                                                 | (b,e) <- bses ]

liftLambda :: CoreBndr -> CoreExpr -> LiftM CoreExpr
liftLambda b e = let vs :: [CoreBndr]
                     e' :: CoreExpr
                     (vs,e') = collectBinders e
                 in  local (++ vs) $ do
                        e'' <- liftExpr e'
                        vs' <- ask
                        return (mkLams vs' e'')

liftExpr :: CoreExpr -> LiftM CoreExpr
liftExpr e = case e of
    Let b lhs -> do
       vs <- ask
       let bs = bindersOf b
           subsList  = [(x,Note (CoreNote "substituted") (mkApps (Var x) (map Var vs)))
                       | x <- bs]
           subst     = extendIdSubstList (mkEmptySubst (mkInScopeSet (bindFreeVars b `unionVarSet` exprFreeVars lhs))) subsList
--                        `extendInScopeList` (vs ++ bs)
           b' :: CoreBind
           e' :: CoreExpr
           Let b' e' = {- trace ("Substituting " ++
                                concat [ show b ++ " to " ++ showSDoc (pprCoreExpr (e :: CoreExpr))
                                       | (b,e) <- subsList ]
                                ++ " in scope : " ++ show vs)
                     $ -} substExpr (error "liftExpr : SDoc") subst e
       liftBndr b'
       -- trace ("SubstExpr is " ++ showSDoc (pprCoreExpr (e' :: CoreExpr))) $
       liftExpr e'
    Lam{}     -> error ("liftExpr on lambda" ++ showSDoc (pprCoreExpr e))
    App e1 e2 -> App <$> liftExpr e1 <*> liftExpr e2
    Case s w t alts -> local (++ [w]) $ (\s' alts' -> Case s' w t alts')
                                                        <$> liftExpr s
                                                        <*> mapM liftAlt alts
    Cast e' c -> (`Cast` c) <$> liftExpr e'
    Note n e' -> Note n <$> liftExpr e'
    _         -> return e

liftAlt :: CoreAlt -> LiftM CoreAlt
liftAlt (con, bs, e) = (,,) con bs <$> local (++ bs) (liftExpr e)
