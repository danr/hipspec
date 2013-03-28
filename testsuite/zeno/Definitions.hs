{-# LANGUAGE DeriveDataTypeable #-}
module Definitions where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),div,return,(.))
import HipSpec.Prelude

data Nat = S Nat | Z
  deriving (Eq,Show,Typeable,Ord)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in (nats !!) `fmap` choose (0,5)

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

-- Boolean functions

otherwise = True

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- Natural numbers
--
(==) :: Nat -> Nat -> Bool
Z   == Z   = True
Z   == S _ = False
S _ == Z   = False
S x == S y = x == y

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
S _ <= Z   = False
S x <= S y = x <= y

(<) :: Nat -> Nat -> Bool
Z   < Z   = False
Z   < S _ = True
S _ < Z   = False
S x < S y = x < y

(+) :: Nat -> Nat -> Nat
Z     + y = y
(S x) + y = S (x + y)

(-) :: Nat -> Nat -> Nat
Z   - Z     = Z
S m - Z     = S m
Z   - S n   = Z
S m - S n   = m - n

min :: Nat -> Nat -> Nat
min Z     Z     = Z
min Z     (S _) = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max :: Nat -> Nat -> Nat
max Z     Z     = Z
max Z     (S y) = S y
max (S x) Z     = S x
max (S x) (S y) = S (max x y)

-- Abstract Lists

data List = Cons A List | Nil
  deriving (Eq,Typeable,Ord)

instance Arbitrary List where
    arbitrary = toList `fmap` arbitrary

fromList :: List -> [A]
fromList (Cons x xs) = x : fromList xs
fromList Nil         = []

toList :: [A] -> List
toList (x:xs) = Cons x (toList xs)
toList []     = Nil

null :: List -> Bool
null Nil         = True
null (Cons _ _)  = False

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

drop :: Nat -> List -> List
drop Z     xs          = xs
drop (S _) Nil         = Nil
drop (S x) (Cons _ xs) = drop x xs

take :: Nat -> List -> List
take Z     xs          = Nil
take (S _) Nil         = Nil
take (S n) (Cons x xs) = Cons x (take n xs)

rev :: List -> List
rev (Cons x xs) = rev xs ++ Cons x Nil
rev Nil         = Nil

len :: List -> Nat
len Nil         = Z
len (Cons _ xs) = S (len xs)

map :: (A -> A) -> List -> List
map f (Cons x xs) = Cons (f x) (map f xs)
map f Nil         = Nil

filter :: (A -> Bool) -> List -> List
filter p (Cons x xs) | p x = Cons x (filter p xs)
                     | otherwise = filter p xs
filter p Nil = Nil

takeWhile :: (A -> Bool) -> List -> List
takeWhile p (Cons x xs) | p x = Cons x (takeWhile p xs)
                        | otherwise = Nil
takeWhile p Nil = Nil

dropWhile :: (A -> Bool) -> List -> List
dropWhile p (Cons x xs) | p x = dropWhile p xs
                        | otherwise = Cons x xs
dropWhile p Nil = Nil


-- Nat lists

data NList = NCons Nat NList | NNil
  deriving (Eq,Typeable,Ord)

instance Arbitrary NList where
    arbitrary = toNList `fmap` arbitrary

fromNList :: NList -> [Nat]
fromNList (NCons x xs) = x : fromNList xs
fromNList NNil         = []

toNList :: [Nat] -> NList
toNList (x:xs) = NCons x (toNList xs)
toNList []     = NNil

(+++) :: NList -> NList -> NList
NCons x xs +++ ys = NCons x (xs +++ ys)
NNil       +++ ys = ys

nnull :: NList -> Bool
nnull NNil         = True
nnull (NCons _ _)  = False

nrev :: NList -> NList
nrev (NCons x xs) = nrev xs +++ NCons x NNil
nrev NNil         = NNil

ndrop :: Nat -> NList -> NList
ndrop Z     xs           = xs
ndrop (S _) NNil         = NNil
ndrop (S x) (NCons _ xs) = ndrop x xs

ntake :: Nat -> NList -> NList
ntake Z     xs           = NNil
ntake (S _) NNil         = NNil
ntake (S n) (NCons x xs) = NCons n (ntake x xs)

nlen :: NList -> Nat
nlen NNil         = Z
nlen (NCons _ xs) = S (nlen xs)

elem :: Nat -> NList -> Bool
elem _ NNil         = False
elem n (NCons x xs)
    | n == x    = True
    | otherwise = elem n xs

delete :: Nat -> NList -> NList
delete _ NNil         = NNil
delete n (NCons x xs)
    | n == x    = delete n xs
    | otherwise = NCons x (delete n xs)

count :: Nat -> NList -> Nat
count n (NCons x xs) | n == x    = S (count n xs)
                     | otherwise = count n xs
count n NNil = Z

sorted :: NList -> Bool
sorted (NCons x (NCons y xs)) = x <= y && sorted (NCons y xs)
sorted _ = True

{- Zeno
insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insort n xs)
-}

insort :: Nat -> NList -> NList
insort n NNil = NCons n NNil
insort n (NCons x xs)
    | n <= x    = NCons n (NCons x xs)
    | otherwise = NCons x (insort n xs)

{- Zeno
ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    _ -> x : (ins n xs)
-}

ins :: Nat -> NList -> NList
ins n NNil = NCons n NNil
ins n (NCons x xs)
    | n < x     = NCons n (NCons x xs)
    | otherwise = NCons x (ins n xs)

{- Zeno
ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n == x of
    True -> x : xs
    _ -> x : (ins1 n xs)
-}

ins1 :: Nat -> NList -> NList
ins1 n NNil = NCons n NNil
ins1 n (NCons x xs)
    | n == x    = NCons x xs
    | otherwise = NCons x (ins1 n xs)

{- Zeno
sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)
-}

sort :: NList -> NList
sort NNil         = NNil
sort (NCons x xs) = insort x (sort xs)

-- Pairs

data Pair = Pair A A deriving (Eq,Typeable,Ord)

instance Arbitrary Pair where
    arbitrary = do
        a <- arbitrary
        b <- arbitrary
        return (Pair a b)

-- Lists of Pairs

data PList = PCons Pair PList | PNil
  deriving (Eq,Typeable,Ord)

instance Arbitrary PList where
    arbitrary = toPList `fmap` arbitrary

fromPList :: PList -> [Pair]
fromPList (PCons x xs) = x : fromPList xs
fromPList PNil         = []

toPList :: [Pair] -> PList
toPList (x:xs) = PCons x (toPList xs)
toPList []     = PNil

zip :: List -> List -> PList
zip (Cons x xs) (Cons y ys) = PCons (Pair x y) (zip xs ys)
zip (Cons _ _)  Nil         = PNil
zip Nil         (Cons _ _)  = PNil
zip Nil         Nil         = PNil

(++++) :: PList -> PList -> PList
PCons x xs ++++ ys = PCons x (xs ++++ ys)
PNil       ++++ ys = ys

prev :: PList -> PList
prev (PCons x xs) = prev xs ++++ PCons x PNil
prev PNil         = PNil

pdrop :: Nat -> PList -> PList
pdrop Z     xs           = xs
pdrop (S _) PNil         = PNil
pdrop (S x) (PCons _ xs) = pdrop x xs

ptake :: Nat -> PList -> PList
ptake Z     xs           = PNil
ptake (S _) PNil         = PNil
ptake (S n) (PCons x xs) = PCons x (ptake n xs)

butlast :: NList -> NList
butlast NNil = NNil
butlast (NCons _ NNil) = NNil
butlast (NCons x xs) = NCons x (butlast xs)

last :: NList -> Nat
last NNil = Z
last (NCons x NNil) = x
last (NCons x xs) = last xs

butlastConcat :: NList -> NList -> NList
butlastConcat xs NNil = butlast xs
butlastConcat xs ys   = xs +++ butlast ys

lastOfTwo :: NList -> NList -> Nat
lastOfTwo xs NNil = last xs
lastOfTwo _  ys   = last ys

zipConcat :: A -> List -> List -> PList
zipConcat _ _  Nil         = PNil
zipConcat x xs (Cons y ys) = PCons (Pair x y) (zip xs ys)

-- Trees

data Tree = Leaf | Node Tree A Tree
  deriving (Eq,Ord,Typeable)

instance Arbitrary Tree where
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

height :: Tree -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree -> Tree
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

