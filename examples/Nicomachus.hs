{-# LANGUAGE DeriveDataTypeable #-}
module Nicomachus where

import Prelude hiding ((+),(*))
import HipSpec.Prelude
import Test.QuickSpec.Signature

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

tri :: Nat -> Nat
tri Z     = Z
tri (S n) = tri n + S n

cubes :: Nat -> Nat
cubes Z     = Z
cubes (S n) = cubes n + (S n * S n * S n)

prop_Nichomachus :: Nat -> Prop Nat
prop_Nichomachus n = cubes n =:= tri n * tri n

infixl 6 +
infixl 7 *

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized arbSized

instance Partial Nat where
  unlifted Z = return Z
  unlifted (S x) = fmap S (lifted x)

arbSized s = do
  x <- choose (0,round (sqrt (toEnum s)))
  return (toEnum x)

