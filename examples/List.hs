{-# LANGUAGE DeriveDataTypeable #-}
module List where

import Prelude hiding (reverse,(++),length)
import HipSpec.Prelude
import Nat hiding (sig)

data List = Cons A List | Nil
  deriving (Eq,Typeable,Ord)

length :: List -> Nat
length Nil         = Z
length (Cons _ xs) = S (length xs)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

instance Arbitrary List where
    arbitrary = toList `fmap` arbitrary

instance Partial List where
    unlifted xs = toList `fmap` unlifted (fromList xs)

fromList :: List -> [A]
fromList (Cons x xs) = x : fromList xs
fromList Nil         = []

toList :: [A] -> List
toList (x:xs) = Cons x (toList xs)
toList []     = Nil

