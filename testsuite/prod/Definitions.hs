{-# LANGUAGE DeriveDataTypeable #-}
{-

    Definitions for the properties in Productive Use Of Failure

-}
module Definitions where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),return)
import HipSpec.Prelude

-- Booleans

otherwise :: Bool
otherwise = True

(&&) :: Bool -> Bool -> Bool
True && x = x
_    && _ = False

(||) :: Bool -> Bool -> Bool
False || x = x
_     || _ = True

not :: Bool -> Bool
not True  = False
not False = True

-- Nats

data Nat = S Nat | Z deriving (Eq,Show,Typeable,Ord)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in (nats !!) `fmap` choose (0,5)

instance Partial Nat where
  unlifted Z = return Z
  unlifted (S x) = fmap S (lifted x)

(+) :: Nat -> Nat -> Nat
Z   + y = y
S x + y = S (x + y)

(*) :: Nat -> Nat -> Nat
Z   * _ = Z
S x * y = y + (x * y)

(==) :: Nat -> Nat -> Bool
Z   == Z   = True
Z   == S _ = False
S _ == Z   = False
S x == S y = x == y

(/=) :: Nat -> Nat -> Bool
x /= y = not (x == y)

(<=) :: Nat -> Nat -> Bool
Z   <= Z   = True
Z   <= S _ = True
S _ <= Z   = False
S x <= S y = x <= y

double :: Nat -> Nat
double Z     = Z
double (S x) = S (S (double x))

even :: Nat -> Bool
even Z         = True
even (S Z)     = False
even (S (S x)) = even x

half :: Nat -> Nat
half Z         = Z
half (S Z)     = Z
half (S (S x)) = S (half x)

mult :: Nat -> Nat -> Nat -> Nat
mult Z     _ acc = acc
mult (S x) y acc = mult x y (y + acc)

fac :: Nat -> Nat
fac Z     = S Z
fac (S x) = S x * fac x

qfac :: Nat -> Nat -> Nat
qfac Z     acc = acc
qfac (S x) acc = qfac x (S x * acc)

exp :: Nat -> Nat -> Nat
exp _ Z     = S Z
exp x (S n) = x * exp x n

qexp :: Nat -> Nat -> Nat -> Nat
qexp x Z     acc = acc
qexp x (S n) acc = qexp x n (x * acc)

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

length :: List -> Nat
length Nil         = Z
length (Cons _ xs) = S (length xs)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

drop :: Nat -> List -> List
drop Z     xs          = xs
drop (S _) Nil         = Nil
drop (S x) (Cons _ xs) = drop x xs

rev :: List -> List
rev (Cons x xs) = rev xs ++ Cons x Nil
rev Nil         = Nil

qrev :: List -> List -> List
qrev Nil         ys = ys
qrev (Cons x xs) ys = qrev xs (Cons x ys)

rotate :: Nat -> List -> List
rotate Z     xs          = xs
rotate (S _) Nil         = Nil
rotate (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

-- Lists of Lists

data LList = LCons List LList | LNil
  deriving (Eq,Typeable,Ord)

instance Arbitrary LList where
    arbitrary = toLList `fmap` arbitrary

fromLList :: LList -> [List]
fromLList (LCons x xs) = x : fromLList xs
fromLList LNil         = []

toLList :: [List] -> LList
toLList (x:xs) = LCons x (toLList xs)
toLList []     = LNil

revflat :: LList -> List
revflat LNil = Nil
revflat (LCons x xs) = revflat xs ++ rev x

qrevflat :: LList -> List -> List
qrevflat LNil         acc = acc
qrevflat (LCons x xs) acc = qrevflat xs (rev x ++ acc)

-- Alternative (more complicated) definitions
revflat' :: LList -> List
revflat' LNil                    = Nil
revflat' (LCons Nil xss)         = revflat xss
revflat' (LCons (Cons x xs) xss) = revflat (LCons xs xss) ++ Cons x Nil

qrevflat' :: LList -> List -> List
qrevflat' LNil                    acc = acc
qrevflat' (LCons Nil xss)         acc = qrevflat xss acc
qrevflat' (LCons (Cons x xs) xss) acc = qrevflat (LCons xs xss) (Cons x acc)

-- Nat lists

data NList = NCons Nat NList | NNil
  deriving (Eq,Typeable,Ord,Show)

instance Arbitrary NList where
    arbitrary = toNList `fmap` arbitrary

fromNList :: NList -> [Nat]
fromNList (NCons x xs) = x : fromNList xs
fromNList NNil         = []

toNList :: [Nat] -> NList
toNList (x:xs) = NCons x (toNList xs)
toNList []     = NNil

elem :: Nat -> NList -> Bool
elem _ NNil         = False
elem n (NCons x xs) = n == x || elem n xs

subset :: NList -> NList -> Bool
subset NNil ys         = True
subset (NCons x xs) ys = x `elem` ys && subset xs ys

intersect :: NList -> NList -> NList
NCons x xs `intersect` ys | x `elem` ys = NCons x (xs `intersect` ys)
                          | otherwise   = xs `intersect` ys
NNil       `intersect` ys = NNil

union :: NList -> NList -> NList
union (NCons x xs) ys | x `elem` ys = union xs ys
                      | otherwise   = NCons x (union xs ys)
union NNil         ys = ys

isort :: NList -> NList
isort NNil         = NNil
isort (NCons x xs) = insert x (isort xs)

insert :: Nat -> NList -> NList
insert n NNil = NCons n NNil
insert n (NCons x xs)
    | n <= x    = NCons n (NCons x xs)
    | otherwise = NCons x (insert n xs)

count :: Nat -> NList -> Nat
count n (NCons x xs) | n == x    = S (count n xs)
                     | otherwise = count n xs
count n NNil = Z

sorted :: NList -> Bool
sorted (NCons x (NCons y xs)) = x <= y && sorted (NCons y xs)
sorted _ = True

(+++) :: NList -> NList -> NList
NCons x xs +++ ys = NCons x (xs +++ ys)
NNil       +++ ys = ys

ndrop :: Nat -> NList -> NList
ndrop Z     xs           = xs
ndrop (S _) NNil         = NNil
ndrop (S x) (NCons _ xs) = ndrop x xs

nlength :: NList -> Nat
nlength NNil         = Z
nlength (NCons _ xs) = S (nlength xs)

