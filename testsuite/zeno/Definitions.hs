{-# LANGUAGE DeriveDataTypeable,FlexibleInstances #-}
module Definitions where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),div,return,(.),Maybe(..))
import HipSpec hiding (signature,constants,instances,None,extraPruner)
import QuickSpec hiding (S,ins)
import QuickSpec.Signature
import QuickSpec.Type

data Nat = S Nat | Z
  deriving (Eq,Show,Typeable,Ord)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in (nats !!) `fmap` choose (0,5)

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq,Ord,Show,Typeable)

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized arbTree
    where
      arbTree 0 = return Leaf
      arbTree n = frequency
        [(1,return Leaf)
        ,(n,do let n' = n `div` 2
               l <- arbTree n'
               x <- arbitrary
               r <- arbTree n'
               return (Node l x r))]

-- Boolean functions

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- Natural numbers

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max Z     y     = y             --
max x     Z     = x
max (S x) (S y) = S (max x y)

-- List functions

null :: [a] -> Bool
null [] = True
null _  = False

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n == x of
    True -> delete n xs
    False -> x : (delete n xs)

len :: [a] -> Nat
len [] = Z
len (_:xs) = S (len xs)

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n == x of
    True -> True
    False -> elem n xs

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take :: Nat -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

butlast :: [a] -> [a]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insort n xs)

ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    _ -> x : (ins n xs)

ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n == x of
    True -> x : xs
    _ -> x : (ins1 n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

butlastConcat :: [a] -> [a] -> [a]
butlastConcat xs [] = butlast xs
butlastConcat xs ys = xs ++ butlast ys

lastOfTwo :: [Nat] -> [Nat] -> Nat
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

