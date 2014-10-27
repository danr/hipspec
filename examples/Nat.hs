{-# LANGUAGE DeriveDataTypeable #-}
module Nat where

import Prelude hiding ((+),(*),(-),(<))
import HipSpec
import QuickSpec hiding (S)
import Data.Typeable

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

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


instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \ s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)

