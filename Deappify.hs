{-# LANGUAGE ViewPatterns,PatternGuards #-}
module Deappify where

import FunctionalFO
import SimpleToFO

import qualified Type as T

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

zapFn :: Function (Var v) -> Zap v (Function (Var v))
zapFn (Function v as b) = Function v as <$> zapBody b

zapBody :: Body (Var v) -> Zap v (Body (Var v))
zapBody b0 = case b0 of
    Case e alts -> Case <$> zapExpr e <*> sequence [ (,) p <$> zapBody b | (p,b) <- alts ]
    Body e      -> Body <$> zapExpr e

zapExpr :: Expr (Var v) -> Zap v (Expr (Var v))
zapExpr e0 k = zap $ case e0 of
    Apply e ts args -> Apply e ts (mapM zapExpr args k)
    _ -> e0
  where
    zap e = case pointer e of
        Just ((x,t,ts),args) | Just arity <- k x, length args == arity ->
            let FOType tvs [] (T.collectArrTy -> (as,r)) = t
                (as',rs') = splitAt arity as
                nt = FOType tvs as' (T.makeArrows rs' r)
            in  Apply (Orig x ::: nt) ts (mapM zapExpr args k)
        _ -> e

pointer :: Expr (Var v) -> Maybe ((v,FOType (FOName v),[FOType (Var v)]),[Expr (Var v)])
pointer e0 = case e0 of
    Apply (Ptr x ::: t) ts []                             -> Just ((x,t,ts),[])
    Apply (App ::: _) _ [e,a] | Just (xt,as) <- pointer e -> Just (xt,as++[a])
    _                                                     -> Nothing

