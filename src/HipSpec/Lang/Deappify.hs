{-# LANGUAGE ViewPatterns,PatternGuards #-}
module HipSpec.Lang.Deappify where

import HipSpec.Lang.FunctionalFO

import HipSpec.Lang.Type

import Control.Applicative


{-
    if we apply app enough times to a ptr, then we can unpointer it

        (f_ptr @ x) @ y = f [x,y],

    when

        f_ptr :: FOType tvs _ (ArrTy t1 (ArrTy t2 _))

    hmm this might not be exactly right. we need the arities of the functions.

        f x = e

    zap needs the source level arities of expressions!

-}

type Zap v a = (v -> Maybe Int) -> a

zapFn :: Function v -> Zap v (Function v)
zapFn fn k = fn { fn_body = zapBody (fn_body fn) k }

zapBody :: Body v -> Zap v (Body v)
zapBody b0 = case b0 of
    Case e alts -> Case <$> zapExpr e <*> sequence [ (,) p <$> zapBody b | (p,b) <- alts ]
    Body e      -> Body <$> zapExpr e

zapExpr :: Expr v -> Zap v (Expr v)
zapExpr e0 k = zap $ case e0 of
    Fun x ts es     -> Fun x ts (mapM zapExpr es k)
    App t1 t2 e1 e2 -> App t1 t2 (zapExpr e1 k) (zapExpr e2 k)
    Ptr{}           -> e0
    Lit{}           -> e0
  where
    zap e = case pointer e of
        Just ((x,ts),args)
            | Just arity <- k x
            , length args == arity
            -> Fun x ts (mapM zapExpr args k)
        _ -> e

pointer :: Expr v -> Maybe ((v,[Type v]),[Expr v])
pointer e0 = case e0 of
    App _ _ fn arg | Just (xt,as) <- pointer fn -> Just (xt,as++[arg])
    Ptr x ts -> Just ((x,ts),[])
    _        -> Nothing

