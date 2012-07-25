module Halo.FOL.MinAsNotUnr(minAsNotUnr) where

import Var

import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract
import Halo.Util (nubSorted)
import Halo.PrimCon
import Halo.PrimCon

import Data.Generics.Uniplate.Data
import Data.Data
import Data.Maybe

minAsNotUnr :: Data (f Var Var) => f Var Var -> f Var Var
minAsNotUnr = transformBi $ \f -> case f of
    Min tm -> tm =/= unr
    e      -> e

