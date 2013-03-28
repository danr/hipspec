module Sorting where

import Prelude(Bool(..))
import HipSpec.Prelude
import Definitions
import Properties(prop_T14)

def :: NList -> NList -> NList
def xs ys = if sorted xs then ys else NNil

prop_def x = def x (NCons Z NNil) =:= NCons Z NNil ==> proveBool (sorted x)
