{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables #-}
module HipSpec.Calls
    ( module VarSet
    , Constructors(..)
    , exprCalls
    , calls
    , transCalls
    , transFrom
    ) where

import CoreSyn
import Id
import VarSet
import CoreFVs
import DataCon
import TyCon

import Lang.Utils
import Lang.Unfoldings
import Lang.FreeTyCons

import qualified Data.Set as S

data Constructors = With | Without deriving Eq

-- | The vars this expression calls
exprCalls :: Constructors -> CoreExpr -> VarSet
exprCalls cons = exprSomeFreeVars $ \ v ->
          (isLocalId v || isGlobalId v || (cons == With && isDataConId v && not (isNewtypeConId v)))
       && (cons == With || not (isDataConId v))

-- | The functions this functions calls (not transitively)
calls :: Constructors -> Id -> VarSet
calls c v = cons `unionVarSet` case maybeUnfolding v of
    Just e -> exprCalls c e
    _      -> emptyVarSet
  where
    cons | c == With = mkVarSet (concatMap (map dataConWorkId .  tyConDataCons)
                                           (S.toList (varTyCons v)))
         | otherwise = emptyVarSet

-- | The functions this function calls transitively
transCalls :: Constructors -> Id -> VarSet
transCalls c = transFrom c . unitVarSet

-- | The transitive closure of calls from this set
transFrom :: Constructors -> VarSet -> VarSet
transFrom c = go emptyVarSet
  where
    go visited queue
        | isEmptyVarSet to_visit = visited
        | otherwise = go (visited `unionVarSet` to_visit)
                         (foldVarSet (\ i vs -> calls c i `unionVarSet` vs)
                                     emptyVarSet
                                     to_visit)
      where to_visit = queue `minusVarSet` visited

