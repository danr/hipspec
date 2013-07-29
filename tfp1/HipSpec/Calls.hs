{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables #-}
-- Calls a function does
-- Looks at the core unfolding, or in an extra-supplied map
module HipSpec.Calls
    ( module VarSet
    , exprCalls
    , calls
    , transCalls
    , transFrom
    ) where

import CoreSyn
import Id
import VarSet
import CoreFVs

import Lang.Unfoldings

-- | The vars this expression calls
exprCalls :: CoreExpr -> VarSet
exprCalls = exprSomeFreeVars $ \ v ->
    (isLocalId v || isGlobalId v) && not (isId v && isConLikeId v)

-- | The functions this functions calls (not transitively)
calls :: Id -> VarSet
calls v = case maybeUnfolding v of
    Just e -> exprCalls e
    _      -> emptyVarSet

-- | The functions this function calls transitively
transCalls :: Id -> VarSet
transCalls = transFrom . unitVarSet

-- | The transitive closure of calls from this set
transFrom :: VarSet -> VarSet
transFrom = go emptyVarSet
  where
    go visited queue
        | isEmptyVarSet to_visit = visited
        | otherwise = go (visited `unionVarSet` to_visit)
                         (foldVarSet (\ i vs -> calls i `unionVarSet` vs)
                                     emptyVarSet
                                     to_visit)
      where to_visit = queue `minusVarSet` visited

