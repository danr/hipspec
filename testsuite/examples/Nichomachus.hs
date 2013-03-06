{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Main where

import Prelude hiding ((+),(*),even,odd,sum,id)
import HipSpec
import HipSpec.Prelude
import Data.Typeable

data Nat = Z | S Nat deriving (Show,Eq,Ord,Typeable)

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
Z   + m = m
S n + m = S (n + m)

(*) :: Nat -> Nat -> Nat
Z   * m = Z
S n * m = m + (n * m)

sum Z     = Z
sum (S n) = sum n + S n

cubes Z     = Z
cubes (S n) = cubes n + (S n * S n * S n)

prop_Nicomachus :: Nat -> Prop Nat
prop_Nicomachus n = cubes n =:= sum n * sum n

main :: IO ()
main = hipSpec $(fileName)
    [ pvars ["x", "y", "z"] (error "Nat type" :: Nat)
    , fun0 "Z" Z
    , fun1 "S" S
    , fun2 "+" (+)
    , fun2 "*" (*)
    , fun1 "sum"   sum
    , fun1 "cubes" cubes
    ]

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)

instance Partial Nat where
  unlifted Z = return Z
  unlifted (S n) = fmap S (lifted n)
