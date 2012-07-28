module Halo.FOL.MinAsNotUnr ( minAsNotUnr ) where

import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract
import Halo.PrimCon

import Data.Generics.Geniplate

minAsNotUnr :: Clause' -> Clause'
minAsNotUnr = transformBi $ \f -> case f of
    Min tm -> tm =/= unr
    e      -> e
