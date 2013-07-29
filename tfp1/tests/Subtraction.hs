module Subtraction where

import Prelude hiding ((-))

data Nat = S Nat | Z

Z   - _   = Z
x   - Z   = x
S x - S y = x - y


