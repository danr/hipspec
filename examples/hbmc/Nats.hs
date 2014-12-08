{-# LANGUAGE DeriveDataTypeable #-}
module Nats where

import Prelude hiding ((+),(*),(-),(<))
import HipSpec
import QuickSpec hiding (S)
import Data.Typeable

data Nat = Z | S Nat deriving (Eq,Ord,Typeable)

instance Show Nat where
  show = show . go
    where
      go Z     = 0
      go (S n) = succ (go n)

infixl 6 -
infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

-- | Truncated subtraction
(-) :: Nat -> Nat -> Nat
S n - S m = n - m
m   - Z   = m
Z   - _   = Z

(<) :: Nat -> Nat -> Bool
Z < _     = True
_ < Z     = False
S n < S m = n < m

plus_idem x = x + x =:= x
mul_idem  x = x * x =:= x

silly x y z = x * (y + z) =:= (x * y) + z

sub_comm  x y   = x - y =:= y - x
sub_assoc x y z = x - (y - z) =:= (x - y) - z

trans x y z = x < y =:= True ==> y < z =:= True ==> x < z =:= True

not_trans x y z = x < y =:= True ==> y < z =:= True ==> x < z =:= False

plus_not_idem x = x + x =:= x ==> True =:= False
true_is_false = True =:= False
