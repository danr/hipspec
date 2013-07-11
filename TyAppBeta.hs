{-# LANGUAGE PackageImports #-}
-- | Beta reduction for types (applied to lambdas)
module TyAppBeta where

import "ghc" Type

import CoreSyn
import qualified CoreSubst as CS
import qualified Outputable

-- | Beta reduction for types (applied to lambdas)
tyAppBeta :: CoreExpr -> CoreExpr
tyAppBeta = go
  where
    go e0 = case e0 of
        App e1 e2 -> case (go e1,go e2) of
            (Lam x e,Type t) -> reduce x e t
            (e1',e2')        -> App e1' e2'
        Lam x e         -> Lam x (go e)
        Tick tk e       -> Tick tk (go e)
        Cast e co       -> Cast (go e) co
        Case e x t alts -> Case (go e) x t [ (p,bs,go rhs) | (p,bs,rhs) <- alts ]
        Let b e         -> Let (go' b) (go e)
        Var{}           -> e0
        Lit{}           -> e0
        Coercion{}      -> e0
        Type{}          -> e0

    go' b = case b of
        NonRec v e -> NonRec v (go e)
        Rec vses   -> Rec [ (v,go e) | (v,e) <- vses ]

-- | Reduces a type variable in an expression by applying it to a type
reduce :: TyVar -> CoreExpr -> Type -> CoreExpr
reduce x e t = CS.substExpr Outputable.empty su e
  where su = CS.extendTvSubst CS.emptySubst x t
