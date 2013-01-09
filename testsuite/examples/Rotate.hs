{-

    While the default settings proves prop_T32 from productive use of
    failure, and some other properties:

        length (rotate n xs) = length xs

        rotate n (rotate m xs) = rotate (n + m) xs

    Use --indvars=3

-}
{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Main where

import Prelude hiding (reverse,(++),(+),length)

import Data.Typeable

import HipSpec
import HipSpec.Prelude

data Nat = S Nat | Z
  deriving (Eq,Show,Typeable,Ord)

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
_   + m = m

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

rotate :: Nat -> [a] -> [a]
rotate Z     xs     = xs
rotate _     []     = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

-- From productive use of failure
prop_T32 :: [a] -> Prop [a]
prop_T32 xs = rotate (length xs) xs =:= xs

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] typeA
    , vars ["n", "m", "o"] natType
    , vars ["xs", "ys", "zs"] listType
    , fun0 "Z"      Z
    , fun1 "S"      S
    , fun2 "+"      (+)
    , fun0 "[]"     ([]       :: [A])
    , fun2 ":"      ((:)      :: A  -> [A] -> [A])
    , fun1 "length" (length   :: [A] -> Nat)
    , fun2 "++"     ((++)     :: [A] -> [A] -> [A])
    , fun2 "rotate" (rotate   :: Nat -> [A] -> [A])
    ]
  where
    typeA     = typeA  :: A
    natType   = natType  :: Nat
    listType  = listType :: [A]

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
