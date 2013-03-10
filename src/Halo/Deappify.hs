{-# LANGUAGE PatternGuards #-}
module Halo.Deappify where

import Var
import Halo.MonoType
import Halo.FOL.Abstract
import Halo.FOL.Internals.Internals

zapApp :: Term' -> Maybe (Var,[Term'],MonoType')
zapApp tm = case tm of
    Ptr f t -> Just (f,[],t)
    App t tm1 tm2
        | Just (f,tms,t'@(TArr _ tr)) <- zapApp tm1
        , t == t' -> Just (f,tms ++ [tm2],tr)
    _ -> Nothing

-- | Removes redundant app on pointers
deappify :: Term' -> Term'
deappify tm0
    | Just (f,tms,TCon{}) <- zapApp tm0 = apply f (map deappify tms)
    | otherwise = case tm0 of
        App t e1 e2 -> App t (deappify e1) (deappify e2)
        Fun v tms   -> Fun v (map deappify tms)
        Ctor v tms  -> Ctor v (map deappify tms)
        Prim p tms  -> Prim p (map deappify tms)
        Proj i v tm -> Proj i v (deappify tm)
        _           -> tm0

-- TODO: bottom deappification:
-- app[A->B](bottom(A),x) = bottom(B)
-- Should probably not be so important because we use exprIsBottom in exprTrans
-- REMEMBER: need to make sure that this is not triggered when we actually add
-- this as an axiom


