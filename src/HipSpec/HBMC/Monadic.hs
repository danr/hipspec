-- Transforms the program to monadic form.
--
-- Assumes all function calls are perfectly saturated.
--
-- Ignores and destroys typing (!)
--
-- Has an environment to understand when a function is pure, and slaps on
-- an extra return after calling it.
{-# LANGUAGE PatternGuards,FlexibleContexts #-}
module HipSpec.HBMC.Monadic (monadic,runMon,monExpr,Mon) where

import HipSpec.HBMC.Utils hiding (lift)

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import HipSpec.Utils

import Data.Generics.Geniplate

import Control.Monad.Reader

runMon = runReaderT

type Mon = ReaderT (Id -> Int -> Bool) Fresh

monadic :: Function Id -> Mon (Function Id)
monadic (Function f _t b) = Function f unpty <$> monExpr b

monExpr :: Expr Id -> Mon (Expr Id)
monExpr e0 = case e0 of
    App{} | (ef,args) <- collectArgs e0 ->
        bindExpr ef $ \ mf ->
        bindExprs args $ \ margs -> do
        p <- ask
        is_pure <- ask
        let r = case ef of
                Gbl f _ _ | is_pure f (length args) -> return . ret
                _                                   -> return
        r (mf `apply` margs)
    Lam x _ e -> Lam x unty <$> monExpr e
    Lcl x _    -> return (ret (Lcl x unty))
    Gbl x _ ts -> return (ret (Gbl x unpty (map (const unty) ts)))
    Lit{}      -> return (ret e0)
    String{}   -> return (ret e0)
    Case s mx alts ->
        bindExpr s $ \ ms ->
        Case ms mx <$> mapM monAlt alts
    Let [] b -> monExpr b
    Let (Function f _ b:fns) e -> do
        mb <- monExpr b
        me <- monExpr (Let fns e)
        lift (mb `bind` Lam f unty me)


monAlt :: Alt Id -> Mon (Alt Id)
monAlt (p,e) = (,) p <$> monExpr e

bindExpr :: Expr Id -> (Expr Id -> Mon (Expr Id)) -> Mon (Expr Id)
bindExpr e k = do
    e' <- monExpr e
    x <- lift tmp
    e'' <- k (Lcl x unty)
    lift (bind e' (Lam x unty e''))

bindExprs :: [Expr Id] -> ([Expr Id] -> Mon (Expr Id)) -> Mon (Expr Id)
bindExprs []     k = k []
bindExprs (e:es) k = bindExpr e $ \ x -> bindExprs es $ \ xs -> k (x:xs)

