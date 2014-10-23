{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module BinLists where

import Prelude hiding ((+), (*), (++), (&&),(||),not)

import HipSpec

import Control.Applicative

data Bin = One | ZeroAnd Bin | OneAnd Bin deriving (Show, Eq, Ord, Typeable)

data Nat = Z | S Nat deriving (Show,Eq,Ord,Typeable)

{-

toNat :: Bin -> Nat
toNat = toNatFrom (S Z)

toNatFrom :: Nat -> Bin -> Nat
toNatFrom k One = k
toNatFrom k (ZeroAnd xs) = toNatFrom (k + k) xs
toNatFrom k (OneAnd xs) = k + toNatFrom (k + k) xs

-}

toNat :: Bin -> Nat
toNat One = S Z
toNat (ZeroAnd xs) = toNat xs + toNat xs
toNat (OneAnd xs) = S (toNat xs + toNat xs)

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
Z   + m = m
S n + m = S (n + m)

(*) :: Nat -> Nat -> Nat
Z * _ = Z
S n * m = m + (n * m)

s :: Bin -> Bin
s One = ZeroAnd One
s (ZeroAnd xs) = OneAnd xs
s (OneAnd xs) = ZeroAnd (s xs)

plus :: Bin -> Bin -> Bin
plus One xs = s xs
plus xs@ZeroAnd{} One = s xs
plus xs@OneAnd{} One = s xs
plus (ZeroAnd xs) (ZeroAnd ys) = ZeroAnd (plus xs ys)
plus (ZeroAnd xs) (OneAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (ZeroAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (OneAnd ys) = ZeroAnd (s (plus xs ys))

prop_s :: Bin -> Prop Nat
prop_s n = toNat (s n) =:= S (toNat n)

prop_plus :: Bin -> Bin -> Prop Nat
prop_plus x y = toNat (x `plus` y) =:= toNat x + toNat y

instance Arbitrary Bin where
  arbitrary = sized arbBin
    where
      arbBin sz = frequency
        [ (1, return One)
        , (sz, ZeroAnd <$> arbBin (sz `div` 2))
        , (sz, OneAnd <$> arbBin (sz `div` 2))
        ]

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \sz -> do
    x <- choose (0,round (sqrt (toEnum sz :: Double)))
    return (toEnum x)

