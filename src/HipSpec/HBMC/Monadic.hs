-- Transforms the program to monadic form.
--
-- Assumes all function calls are fully saturated.
--
-- Ignores and destroys typing (!)
--
-- Thinks every global function is monadic:
-- This could be fixed by making a pass first that adds another layer of
-- return for every global reference not a top-level function
-- (constructors, The, UNR...)
{-# LANGUAGE PatternGuards #-}
module HipSpec.HBMC.Monadic (monadic) where

import HipSpec.HBMC.Utils

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import HipSpec.Utils

unpty :: PolyType Id
unpty = error "Polytype destroyed by HipSpec.HBMC.Monadic"

unty :: Type Id
unty = error "Type destroyed by HipSpec.HBMC.Monadic"

monadic :: Function Id -> Fresh (Function Id)
monadic (Function f _t b) = Function f unpty <$> monExpr b

monExpr :: Expr Id -> Fresh (Expr Id)
monExpr e0 = case e0 of
    App{} | (f,args) <- collectArgs e0 ->
        bindExpr f $ \ mf ->
        bindExprs args $ \ margs ->
        return (mf `apply` margs)
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

tmp = (Derived (Refresh (hid Tmp))) <$> fresh

ret ::  Expr Id -> Expr Id
ret e = Gbl (hid Return) unpty [unty] `app` e

bind :: Expr Id -> Expr Id -> Fresh (Expr Id)
((Gbl (HBMCId Bind) _ _ `App` m) `App` f) `bind` g = do
    x <- tmp
    r <- (f `app` Lcl x unty) `bind` g
    m `bind` Lam x unty r

(Gbl (HBMCId Return) _ _ `App` a) `bind` (Lam x _ b) | occurrences x b <= 1 = return ((a // x) b)
m `bind` f = return (Gbl (hid Bind) unpty [unty,unty] `apply` [m,f])

monAlt :: Alt Id -> Fresh (Alt Id)
monAlt (p,e) = (,) p <$> monExpr e

bindExpr :: Expr Id -> (Expr Id -> Fresh (Expr Id)) -> Fresh (Expr Id)
bindExpr e k = do
    e' <- monExpr e
    x <- tmp
    e'' <- k (Lcl x unty)
    bind e' (Lam x unty e'')

bindExprs :: [Expr Id] -> ([Expr Id] -> Fresh (Expr Id)) -> Fresh (Expr Id)
bindExprs []     k = k []
bindExprs (e:es) k = bindExpr e $ \ x -> bindExprs es $ \ xs -> k (x:xs)

