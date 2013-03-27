{-# LANGUAGE DeriveDataTypeable #-}
module PrecisionRecall where

import Prelude (fmap,return,round,sqrt,toEnum,fromEnum,Bool(..),Eq,Ord,Enum,otherwise,succ,pred)

import Data.Typeable

import HipSpec.Prelude

data Nat = Z | S Nat deriving (Eq,Ord,Typeable)

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

data List = Cons A List | Nil
  deriving (Eq,Typeable,Ord)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

foldl :: (A -> A -> A) -> A -> List -> A
foldl op e Nil         = e
foldl op e (Cons x xs) = foldl op (op e x) xs

foldr :: (A -> A -> A) -> A -> List -> A
foldr op e Nil         = e
foldr op e (Cons x xs) = op x (foldr op e xs)

length :: List -> Nat
length Nil         = Z
length (Cons _ xs) = S (length xs)

map :: (A -> A) -> List -> List
map f (Cons x xs) = Cons (f x) (map f xs)
map f Nil         = Nil

filter :: (A -> Bool) -> List -> List
filter p (Cons x xs) | p x = Cons x (filter p xs)
                     | otherwise = filter p xs
filter p Nil = Nil

reverse :: List -> List
reverse (Cons x xs) = reverse xs ++ Cons x Nil
reverse Nil         = Nil

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

instance Arbitrary List where
    arbitrary = toList `fmap` arbitrary

fromList :: List -> [A]
fromList (Cons x xs) = x : fromList xs
fromList Nil         = []

toList :: [A] -> List
toList (x:xs) = Cons x (toList xs)
toList []     = Nil

