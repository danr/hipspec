module Nat where

import Prelude (Eq(..),Bool(..))

data Nat = S Nat | Z deriving (Eq)

succ x = S x

succ' = S

Z   + y = y
S x + y = S (x + y)

S x ++ y = S (x ++ y)
_   ++ y = y