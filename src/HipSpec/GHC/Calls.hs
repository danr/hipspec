{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables,RecordWildCards #-}
module HipSpec.GHC.Calls
    ( module VarSet
    , CallParams(..)
    , Constructors(..)
    , without
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

import HipSpec.GHC.Utils
import HipSpec.GHC.Unfoldings
import HipSpec.GHC.FreeTyCons

import qualified Data.Set as S

data CallParams = CallParams
    { constructors :: Constructors
    , ignore_set   :: VarSet
    }

without :: CallParams
without= CallParams Without emptyVarSet

data Constructors = With | Without deriving Eq

-- | The vars this expression calls
exprCalls :: CallParams -> CoreExpr -> VarSet
exprCalls CallParams{..} = ((`minusVarSet` ignore_set) .) . exprSomeFreeVars $ \ v ->
          (isLocalId v || isGlobalId v || (constructors == With && isDataConId v && not (isNewtypeConId v)))
       && (constructors == With || not (isDataConId v))

-- | The functions this functions calls (not transitively)
calls :: CallParams -> Id -> VarSet
calls c@CallParams{..} v = cons `unionVarSet` case maybeUnfolding v of
    Just e -> exprCalls c e
    _      -> emptyVarSet
  where
    cons | constructors == With = mkVarSet (concatMap (map dataConWorkId .  tyConDataCons)
                                           (S.toList (varTyCons v)))
         | otherwise = emptyVarSet

-- | The functions this function calls transitively
transCalls :: CallParams -> Id -> VarSet
transCalls c = transFrom c . unitVarSet

-- | The transitive closure of calls from this set
transFrom :: CallParams -> VarSet -> VarSet
transFrom c = go emptyVarSet
  where
    go visited queue
        | isEmptyVarSet to_visit = visited
        | otherwise = go (visited `unionVarSet` to_visit)
                         (foldVarSet (\ i vs -> calls c i `unionVarSet` vs)
                                     emptyVarSet
                                     to_visit)
      where to_visit = queue `minusVarSet` visited

