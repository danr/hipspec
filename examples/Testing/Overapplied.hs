module Overapplied where

import HipSpec.Prelude

{-# NOINLINE f #-}
f :: Bool -> A -> A
f True  = error "bla"
f False = error "bli"

prop_f x = f False x =:= f True x

