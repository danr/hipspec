module CoreTest where

import Prelude (Bool(..))

data Nat = Z | S Nat

pred :: Nat -> Nat
pred Z = Z
pred (S x) = x

pred_wild' :: Nat -> Nat
pred_wild' (S x) = x
pred_wild' _ = Z

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

--Z     <= _     = True
--_     <= Z     = False
--(S x) <= (S y) = x <= y
--
--_     < Z     = False
--Z     < _     = True
--(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

--Z     - _     = Z
--x     - Z     = x
--(S x) - (S y) = x - y

Z     * _ = Z
(S x) * y = y + (x * y)

min Z     _     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

--max Z     y     = y
--max x     Z     = x
--max (S x) (S y) = S (max x y)

infix 0 =:=

data Prop a = a :=: a

(=:=) = (:=:)

prop_assoc_plus :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_plus x y z = x + (y + z) =:= (x + y) + z
