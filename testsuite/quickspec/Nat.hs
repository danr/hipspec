{-# LANGUAGE DeriveDataTypeable, TypeFamilies, CPP #-}
module Main where

import Data.Typeable

import Hip.HipSpec

import Test.QuickCheck hiding (Prop)
import Test.QuickSpec

import Prelude hiding ((+),(*),even,odd,pred,sum,id)
import qualified Prelude as P

data Nat = Z | S Nat deriving (Show,Eq,Ord,Typeable)

type Prop a = a

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
Z   + m = m
S n + m = n + S m -- S (n + m)

(*) :: Nat -> Nat -> Nat
Z   * m = Z
S n * m = m + (n * m)

main = hipSpec "Nat.hs" conf 3
  where conf = describe "Nats"
               [ var "x" natType
               , var "y" natType
               , var "z" natType
               , con "Z" Z
               , con "S" S
               , con "+" (+)
               -- , con "*" (*)
               ]
           where natType = (error "Nat type" :: Nat)

prop_assoc :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc x y z = x + (y + z) =:= (x + y) + z

infix 0 =:=
(=:=) = (=:=)

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (P.pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return

