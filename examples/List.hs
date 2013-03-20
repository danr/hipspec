{-# LANGUAGE DeriveDataTypeable #-}
module List where

import Prelude hiding (reverse,(++),length,map,filter,(.),(+),const)
import qualified Prelude
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

map :: (A -> A) -> List -> List
map f (Cons x xs) = Cons (f x) (map f xs)
map f Nil         = Nil

filter :: (A -> Bool) -> List -> List
filter p (Cons x xs) | p x = Cons x (filter p xs)
                     | otherwise = filter p xs
filter p Nil = Nil

(.) :: (A -> A) -> (A -> A) -> (A -> A)
f . g = \ x -> f (g x)

sig = [ vars ["m", "n", "o"]    (undefined :: Nat)
      , vars ["x", "y", "z"]    (undefined :: A)
      , vars ["xs", "ys", "zs"] (undefined :: List)
      , vars ["f", "g"]    (undefined :: A -> A)
      , fun0 "Z" Z
      , fun1 "S" S
      , fun2 "+" (+)
      , fun0 "Nil" Nil
      , fun2 "Cons" Cons
      , fun2 "++" (++)
      , fun2 "map" map
      , fun1 "length" length
      , blind2 "." (.)
      , vars ["p", "q"]         (undefined :: A -> Bool)
      , fun2 "filter" filter
      ]

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

