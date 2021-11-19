{-# LANGUAGE DeriveDataTypeable,FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module PrecisionRecall where

import Prelude (fmap,return,round,sqrt,toEnum,fromEnum,Bool(..),Eq,Ord,Enum,otherwise,succ,pred,Double,($))

import Data.Typeable

import HipSpec

data Nat = Z | S Nat deriving (Eq,Ord,Typeable)

instance Names (A -> A -> A) where
    names _ = ["<>","<+>","<*>"]

instance Names (A -> A) where
    names _ = ["f","g","h"]

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * _ = Z

foldl :: (a -> a -> a) -> a -> [a] -> a
foldl _  e []      = e
foldl op e (x: xs) = foldl op (op e x) xs

foldr :: (a -> a -> a) -> a -> [a] -> a
foldr _  e []     = e
foldr op e (x:xs) = op x (foldr op e xs)

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

map :: (a -> a) -> [a] -> [a]
map f (x:xs) = f x:map f xs
map _ []     = []

filter :: (a -> Bool) -> [a] -> [a]
filter p (x:xs) | p x       = x:filter p xs
                | otherwise = filter p xs
filter _ [] = []

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []     = []

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \ s -> do
      x <- choose (0,round (sqrt (toEnum s :: Double)))
      return (toEnum x)

