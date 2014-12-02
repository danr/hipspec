{-# LANGUAGE DeriveDataTypeable #-}
module Mergesort where

import Prelude (Bool(..),undefined,Ordering(..), (&&), (||), otherwise, not, fmap, Eq, Ord, fst, snd)
import HipSpec
import Nat
import List ((++))
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
msort xs  = merge (msort (evens xs)) (msort (odds xs))

evens :: [Nat] -> [Nat]
evens [] = []
evens [x] = [x]
evens (x:y:rs) = x:evens rs

odds :: [Nat] -> [Nat]
odds [] = []
odds [x] = []
odds (x:y:rs) = y:odds rs

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

uncurry f (x,y) = f x y

prop_merge_sorted xs ys = sorted xs =:= True ==> sorted ys =:= True ==> sorted (merge xs ys) =:= True

prop_atotal a b = a <= b || b <= a =:= True

prop_msort_sorted xs = sorted (msort xs) =:= True

prop_msort_permutation xs x = count x xs =:= count x (msort xs)

prop_count_split x xs = count x (evens xs ++ odds xs) =:= count x xs
