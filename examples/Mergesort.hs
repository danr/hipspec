{-# LANGUAGE DeriveDataTypeable #-}
module Mergesort where

import Prelude (Bool(..),undefined,Ordering(..), (&&), otherwise, not, fmap, Eq, Ord)
import HipSpec
import Nat
import Test.QuickSpec.Signature hiding (ord)
import Test.QuickSpec
import Test.QuickSpec.Prelude
import Test.QuickCheck hiding ((==>))
import GHC.Types
import Data.Typeable

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
S _ <= Z   = False
S x <= S y = x <= y

count :: Nat -> [Nat] -> Nat
count n [] = Z
count n (x:xs)
  | n <= x && x <= n = S (count n xs)
  | otherwise = count n xs

msort :: [Nat] -> [Nat]
msort []  = []
msort [x] = [x]
msort xs  = merge (msort ys) (msort zs)
  where (ys,zs) = split xs

{-
qsort :: [Nat] -> [Nat]
qsort [] = []
qsort (x:xs) = ...
-}

split :: [Nat] -> ([Nat],[Nat])
split [] = ([],[])
split [x] = ([x],[])
split (x:y:rs) = (x:xs,y:ys)
  where (xs,ys) = split rs

merge :: [Nat] -> [Nat] -> [Nat]
merge (x:xs) (y:ys)
    | x <= y = x:merge xs (y:ys)
    | True   = y:merge (x:xs) ys
merge xs [] = xs
merge [] ys = ys

sorted :: [Nat] -> Bool
sorted (x:y:xs)
  | x <= y    = sorted (y:xs)
  | otherwise = False
sorted _      = True

{-
ordered :: [Nat] -> Bool
ordered []     = True
ordered (x:xs) = ord x xs

ord :: Nat -> [Nat] -> Bool
ord x [] = True
ord x (y:ys) = if x <= y then ord y ys else False

prop_merge_ord a b xs ys = ord a xs =:= True ==> ord b ys =:= True ==> ord (min a b) (merge xs ys) =:= True
prop_merge_ordered xs ys = ordered xs =:= True ==> ordered ys =:= True ==> ordered (merge xs ys) =:= True
-}

prop_merge_sorted_lemma x y xs ys =
    x <= y =:= True ==> sorted xs =:= True ==> sorted (y:ys) =:= True ==>
    sorted (x:merge xs ys) =:= True ==>
    sorted (merge xs (y:ys)) =:= True


prop_merge_sorted xs ys = sorted xs =:= True ==> sorted ys =:= True ==> sorted (merge xs ys) =:= True

prop_msort_sorted xs = sorted (msort xs) =:= True

-- prop_msort_permutation xs x = count x xs =:= count x (msort xs)
