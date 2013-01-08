{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
module Main where

import Hip.HipSpec
import Prelude hiding ((+), (*), (++), (&&),(||),not)
import Data.Typeable
import Test.QuickCheck hiding (Prop)
import Control.Applicative

data Bin = Zero | ZeroAnd Bin | OneAnd Bin deriving (Show, Eq, Ord, Typeable)

data Nat = Z | S Nat deriving (Show,Eq,Ord,Typeable)

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
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
  evaluate x = count 100 x `seq` return x
    where count 0 _ = undefined
          count n Z = ()
          count n (S x) = count (n-1) x


{-toNat :: Bin -> Nat
toNat = toNatFrom (S Z)

toNatFrom :: Nat -> Bin -> Nat
toNatFrom k One = k
toNatFrom k (ZeroAnd xs) = toNatFrom (k + k) xs
toNatFrom k (OneAnd xs) = k + toNatFrom (k + k) xs-}

toNat :: Bin -> Nat
toNat Zero = Z
toNat (ZeroAnd xs) = toNat xs + toNat xs
toNat (OneAnd xs) = S (toNat xs + toNat xs)

infixl 6 +
-- infixl 7 *

(+) :: Nat -> Nat -> Nat
Z   + m = m
S n + m = S (n + m)

-- (*) :: Nat -> Nat -> Nat
-- Z * m = Z
-- S n * m = m + (n * m)

s :: Bin -> Bin
s Zero = OneAnd Zero
s (ZeroAnd xs) = OneAnd xs
s (OneAnd xs) = ZeroAnd (s xs)

plus :: Bin -> Bin -> Bin
plus Zero xs = xs
plus xs Zero = xs
plus (ZeroAnd xs) (ZeroAnd ys) = ZeroAnd (plus xs ys)
plus (ZeroAnd xs) (OneAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (ZeroAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (OneAnd ys) = ZeroAnd (s (plus xs ys))

prop_s :: Bin -> Prop Nat
prop_s n = toNat (s n) =:= S (toNat n)

prop_s2 :: Bin -> Bin -> Prop Bin
prop_s2 x y = plus x (s y) =:= s (plus x y)

prop_plus :: Bin -> Bin -> Prop Nat
prop_plus x y = toNat (x `plus` y) =:= toNat x + toNat y

main = hipSpec "BinLists2.hs" conf 3
  where conf = [ var "x"        natType
               , var "y"        natType
               , var "z"        natType
               , var "x"        boolType
               , var "y"        boolType
               , var "z"        boolType
               , var "xs"       listType
               , var "ys"       listType
               , var "zs"       listType
               , con "Z" Z
               , con "S" S
               , con "+" (+)
               -- , con "*" (*)
               , con "s" s
               , con "plus" plus
               , con "Zero" Zero
               , con "ZeroAnd" ZeroAnd
               , con "OneAnd" OneAnd
               , con "toNat" toNat
--               , con "toNatFrom" toNatFrom
                ]
                  where
                    boolType  = undefined :: Bool
                    natType   = undefined :: Nat
                    listType  = undefined :: Bin

instance Arbitrary Bin where
  arbitrary = sized arbBin
    where arbBin s = frequency [(1, return Zero),
                                (s, ZeroAnd <$> arbBin (s-1)),
                                (s, OneAnd <$> arbBin (s-1))]

instance Classify Bin where
  type Value Bin = Bin
  evaluate = return

-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
