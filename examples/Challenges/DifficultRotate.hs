{-# LANGUAGE DeriveDataTypeable #-}
module Challenges.DifficultRotate where

import Prelude hiding (reverse,(++),(+),(*),(-),(<),(<=),length,drop,take)

import HipSpec.Prelude

data List = Cons A List | Nil
  deriving (Eq,Typeable,Ord)

data Nat = S Nat | Z
  deriving (Eq,Show,Typeable,Ord)

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
_   * m = Z

Z   <= _   = True
_   <= Z   = False
S x <= S y = x <= y

_   < Z   = False
Z   < _   = True
S x < S y = x < y

Z   - _   = Z
x   - Z   = x
S x - S y = x - y

n % Z = Z
n % m
    | n < m     = n
    | otherwise = (n - m) % m

length :: List -> Nat
length Nil         = Z
length (Cons _ xs) = S (length xs)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

rotate :: Nat -> List -> List
rotate Z     xs          = xs
rotate _     Nil         = Nil
rotate (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

take :: Nat -> List -> List
take Z     xs          = Nil
take _     Nil         = Nil
take (S n) (Cons x xs) = Cons x (take n xs)

drop :: Nat -> List -> List
drop Z     xs          = xs
drop _     Nil         = Nil
drop (S n) (Cons x xs) = drop n xs

-- From productive use of failure
prop_T32 :: List -> Prop List
prop_T32 xs = rotate (length xs) xs =:= xs

prop_rot_self :: Nat -> List -> Prop List
prop_rot_self n xs = rotate n (xs ++ xs) =:= rotate n xs ++ rotate n xs

prop_rot_mod :: Nat -> List -> Prop List
prop_rot_mod n xs = rotate n xs =:= drop (n % length xs) xs ++ take (n % length xs) xs

sig =
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["n", "m", "o"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: List)
    , fun0 "True"   True
    , fun0 "False"  False
    , fun0 "Z"      Z
    , fun1 "S"      S
    , fun2 "+"      (+)
    , fun2 "*"      (*)
    , fun2 "%"      (%)
    , fun2 "-"      (-)
    , fun2 "<"      (<)
    , fun0 "Nil"    Nil
    , fun2 "Cons"   Cons
    , fun1 "length" length
    , fun2 "++"     (++)
    , fun2 "rotate" rotate
    , fun2 "take"   take
    , fun2 "drop"   drop
    ]

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

instance Partial List where
    unlifted xs = toList `fmap` unlifted (fromList xs)

fromList :: List -> [A]
fromList (Cons x xs) = x : fromList xs
fromList Nil         = []

toList :: [A] -> List
toList (x:xs) = Cons x (toList xs)
toList []     = Nil

