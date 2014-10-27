module GCD where

import Prelude hiding ((-),(+),(*),(<),gcd)
import HipSpec
import Nat

gcd x Z = x
gcd Z x = x
gcd x y | x < y     = gcd x (y - x)
        | otherwise = gcd (x - y) y

