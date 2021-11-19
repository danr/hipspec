{-# LANGUAGE DeriveDataTypeable #-}
module Reverse where

import Prelude hiding ((++))
import HipSpec.Prelude

data List = Cons A List | Nil
  deriving (Eq,Typeable,Ord)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

rev :: List -> List
rev (Cons x xs) = rev xs ++ Cons x Nil
rev Nil         = Nil

revacc :: List -> List -> List
revacc Nil         acc = acc
revacc (Cons x xs) acc = revacc xs (Cons x acc)

qrev :: List -> List
qrev xs = revacc xs Nil

prop_equal    :: List -> Prop List
prop_equal xs = rev xs =:= qrev xs

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

