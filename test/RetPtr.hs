module RetPtr where

import Prelude()

data Nat = Z | S Nat

id x = x

weird Z = S
weird (S Z) = id
weird (S x) = weird x
