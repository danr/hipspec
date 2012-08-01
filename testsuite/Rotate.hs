{-

    While the default settings proves prop_T32 from productive use of
    failure, and some other spectacular properties:

        length (rotate n xs) = length xs

        rotate n (rotate m xs) = rotate (n + m) xs

    Use --indvars=3, and vampire and maybe some generous timeout

-}
{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Prelude hiding (reverse,(++),(+),length)

import Data.Typeable

import Hip.HipSpec
import Hip.Prelude

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

main = hipSpec "Rotate.hs" conf
  where
    conf = [ vars ["x", "y", "z"] intType
           , vars ["n", "m", "o"] natType
           , vars ["xs", "ys", "zs"] listType
           , fun0 "Z"      Z
           , fun1 "S"      S
           , fun2 "+"      (+)
           , fun0 "[]"     ([]       :: [Int])
           , fun2 ":"      ((:)      :: Int  -> [Int] -> [Int])
           , fun1 "length" (length   :: [Int] -> Nat)
           , fun2 "++"     ((++)     :: [Int] -> [Int] -> [Int])
           , fun2 "rotate" (rotate   :: Nat -> [Int] -> [Int])
           ]

    intType   = intType  :: Int
    natType   = natType  :: Nat
    listType  = listType :: [Int]

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
