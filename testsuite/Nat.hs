{-# LANGUAGE DeriveDataTypeable, TypeFamilies, CPP #-}
module Main where

import Prelude hiding ((+),(*),even,odd,sum,id)

import Data.Typeable

import Hip.HipSpec
import Hip.Prelude

{-# ANN type Nat "Nat" #-}
{-# ANN Z "Z" #-}
{-# ANN S "S" #-}
data Nat = Z | S Nat
  deriving (Eq,Ord,Show,Typeable)

infixl 6 +
infixl 7 *

{-# ANN (+) "+" #-}
(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
_   + m = m

{-# ANN (*) "*" #-}
(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
_   * m = Z

prop_mul_comm :: Nat -> Nat -> Nat -> Prop Nat
prop_mul_comm x y z = x * y =:= y * x

main = hipSpec "Nat.hs" conf 3
  where conf = describe "Nats"
               [ var "x" natType
               , var "y" natType
               , var "z" natType
               , con "Z" Z
               , con "S" S
               , con "+" (+)
               , con "*" (*)
               ]
           where natType = (error "Nat type" :: Nat)


instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized arbSized

arbSized s = do
  x <- choose (0,round (sqrt (toEnum s)))
  return (toEnum x)

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return

