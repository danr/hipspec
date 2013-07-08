module Defaults where

import Prelude hiding ((-))

{-

data ABC = A | B | C

le A _ = True
le _ C = True
le B B = True
le _ _ = False

data U a = S (U a) | Z | R a

m Z     _     = Z
m x     Z     = x
m (R _) x     = x
m _     (R a) = R a
m (S x) (S y) = m x y

-}

data Nat a = Succ (Nat a) | Zero

Zero   - _      = Zero
x      - Zero   = x
Succ x - Succ y = x - y
