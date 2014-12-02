{-# LANGUAGE DeriveDataTypeable #-}
module Mergesort where

import Prelude hiding ((++),uncurry)
import HipSpec
import List ((++))
import Test.QuickCheck hiding ((==>))
import GHC.Types
import Data.Typeable

count :: Integer -> [Integer] -> Integer
count n [] = 0
count n (x:xs)
  | n == x = 1 + count n xs
  | otherwise = count n xs

msort :: [Integer] -> [Integer]
msort []  = []
msort [x] = [x]
msort xs  = merge (msort ys) (msort zs)
  where (ys,zs) = split xs

split :: [Integer] -> ([Integer],[Integer])
split [] = ([],[])
split (x:rs) = (x:ys,xs)
  where (xs,ys) = split rs

merge :: [Integer] -> [Integer] -> [Integer]
merge (x:xs) (y:ys)
    | x <= y = x:merge xs (y:ys)
    | True   = y:merge (x:xs) ys
merge xs [] = xs
merge [] ys = ys

sorted :: [Integer] -> Bool
sorted (x:y:xs)
  | x <= y    = sorted (y:xs)
  | otherwise = False
sorted _      = True

uncurry f (x,y) = f x y

prop_merge_sorted xs ys = sorted xs =:= True ==> sorted ys =:= True ==> sorted (merge xs ys) =:= True

prop_msort_sorted xs = sorted (msort xs) =:= True

prop_msort_permutation xs x = count x xs =:= count x (msort xs)

prop_count_split x xs = count x (uncurry (++) (split xs)) =:= count x xs
