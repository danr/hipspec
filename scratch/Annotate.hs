{-# LANGUAGE TemplateHaskell #-}
module Annotate where

{-# ANN Succ "Succ" #-}
g
{-# ANN type Nat "Nat" #-}
data Nat = Succ Nat | Zero

{-# ANN foo "foo" #-}
foo x = x