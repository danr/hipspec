-- Transforms the program to monadic form.
--
-- Assumes all function calls are perfectly saturated.
--
-- Ignores and destroys typing (!)
--
-- Has an environment to understand when a function is pure, and slaps on
-- an extra return after calling it.
{-# LANGUAGE PatternGuards,FlexibleContexts #-}
module HipSpec.HBMC.Monadic (monadic,runMon) where

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

unpty :: PolyType Id
unpty = error "Polytype destroyed by HipSpec.HBMC.Monadic"

unty :: Type Id
unty = error "Type destroyed by HipSpec.HBMC.Monadic"

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
        mb `bind` Lam f unty me

tmp = (Derived (Refresh (hid Tmp))) <$> lift fresh

ret ::  Expr Id -> Expr Id
ret e = Gbl (hid Return) unpty [unty] `app` e

bind :: Expr Id -> Expr Id -> Mon (Expr Id)
((Gbl (HBMCId Bind) _ _ `App` m) `App` f) `bind` g = do
    x <- tmp
    r <- (f `app` Lcl x unty) `bind` g
    m `bind` Lam x unty r

(Gbl (HBMCId Return) _ _ `App` a) `bind` (Lam x _ b) | occurrences x b <= 1 = return ((a // x) b)
m `bind` f = return (Gbl (hid Bind) unpty [unty,unty] `apply` [m,f])

monAlt :: Alt Id -> Mon (Alt Id)
monAlt (p,e) = (,) p <$> monExpr e

bindExpr :: Expr Id -> (Expr Id -> Mon (Expr Id)) -> Mon (Expr Id)
bindExpr e k = do
    e' <- monExpr e
    x <- tmp
    e'' <- k (Lcl x unty)
    bind e' (Lam x unty e'')

bindExprs :: [Expr Id] -> ([Expr Id] -> Mon (Expr Id)) -> Mon (Expr Id)
bindExprs []     k = k []
bindExprs (e:es) k = bindExpr e $ \ x -> bindExprs es $ \ xs -> k (x:xs)

