{-# LANGUAGE PatternGuards #-}
module Halo.Deappify where

import Var
import Id
import Halo.MonoType
import Halo.FOL.Abstract

-- | Tries to collect a pointer application here,
--   returning the pointer applied to terms and their residual type
--   (so you can reappify them)
collectPtrApps :: Term' -> Maybe (Var,[(Term',MonoType')])
collectPtrApps tm = case tm of
    App ty tm1 tm2 -> do
        (f,as) <- collectPtrApps tm1
        return (f,(tm2,ty):as)
    Ptr f _ -> Just (f,[])
    _ -> Nothing

-- | Reapplies residual applications.
--   All terms are assumed to be deappified already.
reapply :: Term' -> [(Term',MonoType')] -> Term'
reapply tm [] = tm
reapply tm ((t,ty):tms) = reapply (app ty t tm) tms

-- | Removes redundant app on pointers
deappify :: Term' -> Term'
deappify tm0
    | Just (f,tytms) <- collectPtrApps tm0  =
        let arity = idArity f
            tytms' = map (first deappify) tytms
            inner = take arity tytms'
            outer = drop arity tytms'
        reapply (apply f (map fst inner)) outer
    | otherwise = case tm0 of
        App e1 e2   -> App (deappify e1) (deappify e2)
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


