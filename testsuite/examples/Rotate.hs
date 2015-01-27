{-# LANGUAGE DeriveDataTypeable #-}
module Rotate where

import Prelude hiding ((++),length)
import HipSpec

data List = Cons A List | Nil
  deriving (Eq,Typeable,Ord)

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

length :: List -> Nat
length Nil         = Z
length (Cons _ xs) = S (length xs)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

rotate :: Nat -> List -> List
rotate Z     xs          = xs
rotate (S _) Nil         = Nil
rotate (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

-- T32 from productive use of failure
prop_T32 :: List -> Prop List
prop_T32 xs = rotate (length xs) xs =:= xs

instance Arbitrary List where
    arbitrary = toList `fmap` arbitrary

fromList :: List -> [A]
fromList (Cons x xs) = x : fromList xs
fromList Nil         = []

toList :: [A] -> List
toList (x:xs) = Cons x (toList xs)
toList []     = Nil

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

