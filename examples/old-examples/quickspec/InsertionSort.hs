{-# LANGUAGE TypeFamilies, DeriveDataTypeable #-}
module Main where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..), undefined, return)
import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Data.Typeable

data Nat = Z | S Nat
  deriving (Eq,Ord,Show, Typeable)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,25)

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return

-- Insertion sort for natural numbers -----------------------------------------

Z     == Z     = True
(S x) == (S y) = x == y
_     == _     = False

Z     <= _     = True
(S x) <= (S y) = x <= y
_     <= _     = False

x < y = x <= y && not (x == y)

not True = False
not _ = True

Z + x = x
S x + y = S (x + y)

True  && a = a
_ && _ = False

length :: [Nat] -> Nat
length [] = Z
length (_:xs) = S (length xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insert n xs)

sorted :: [Nat] -> Bool
sorted (x:y:xs) = x <= y && sorted (y:xs)
sorted _ = True

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insert x (sort xs)

prop_sort_idem :: [Nat] -> Prop [Nat]
prop_sort_idem xs = sort (sort xs) =:= sort xs

prop_length_sort :: [Nat] -> Prop Nat
prop_length_sort xs = length (sort xs) =:= length xs

prop_sorted_sort :: [Nat] -> Prop Bool
prop_sorted_sort xs = sorted (sort xs) =:= True

bothSorted :: [Nat] -> [Nat] -> Bool
bothSorted xs ys = sorted xs && sorted ys

-- Tests ----------------------------------------------------------------------

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

main = hipSpec "InsertionSort.hs" conf 3
  where conf = describe "Lists"
                [ var "x"        intType
                , var "y"        intType
                , var "z"        intType
                , var "xs"       listType
                , var "ys"       listType
                , var "zs"       listType
                , con "[]"       ([]       :: [Nat])
                , con ":"        ((:)      :: Nat  -> [Nat] -> [Nat])
                , con "++"       ((++)     :: [Nat] -> [Nat] -> [Nat])
--                , con "+" (+)
                , con "length"   length
                , con "insert"   insert
                , con "sort"     sort
                , con "sorted"     sorted
                , con "Z" Z, con "S" S
                , con "True" True
--                , con "&&" (&&), con "not" not, con "True" True, con "False" False, var "x" False, var "y" False, var "z" False
--                , con "<=" (<=), con "<" (<)
--                , con "bothSorted" bothSorted
                ]
                   where
                     intType   = undefined :: Nat
                     listType  = undefined :: [Nat]

-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
