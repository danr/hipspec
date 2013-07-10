module Ordinals where

import Prelude ()

data Nat = Z | S Nat

Z + y = y
(S x) + y = S (x + y)

Z * _ = Z
(S x) * y = y + (x * y)

data Ord = Zero | Suc Ord | Lim (Nat -> Ord)

(++) :: Ord -> Ord -> Ord
Zero ++ y = y
Suc x ++ y = Suc (x ++ y)
Lim f ++ y = Lim (\n -> f n ++ y)

(**) :: Ord -> Ord -> Ord
Zero ** y = Zero
Suc x ** y = y ++ (x ** y)
Lim f ** y = Lim (\ n -> f n ** y)

