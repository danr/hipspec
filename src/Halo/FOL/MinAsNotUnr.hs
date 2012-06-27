{-# LANGUAGE ExplicitForAll,ScopedTypeVariables #-}
module Halo.FOL.MinAsNotUnr(minAsNotUnr) where

import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract
import Halo.Util (nubSorted)
import Halo.PrimCon

import Data.Generics.Uniplate.Data
import Data.Data
import Data.Maybe

minAsNotUnr :: forall f q v . (Data (f q v),Data q,Data v) => f q v -> f q v
minAsNotUnr = transformBi f
  where
    f :: Formula q v -> Formula q v
    f (Min tm) = tm =/= constant UNR
    f e        = e

