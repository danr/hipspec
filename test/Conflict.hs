module Conflict where

import Prelude(Bool(..))

data Nat = Zero | Succ Nat

g x = case x of
        Zero -> case x of
                   Zero   -> True
                   Succ _ -> False
        Succ x -> g x
