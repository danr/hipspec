{-# LANGUAGE DeriveDataTypeable #-}
module Mergesort where

import Prelude hiding ((++),uncurry,length,take,drop)
import HipSpec
import List ((++))
import Test.QuickCheck hiding ((==>))
import GHC.Types
import Data.Typeable

length :: [a] -> Integer
length []     = 0
length (_:xs) = 1 + length xs

take :: Integer -> [a] -> [a]
take n xs | n <= 0 = []
take n []     = []
take n (x:xs) = x:take (n-1) xs

drop :: Integer -> [a] -> [a]
drop n xs | n <= 0 = xs
drop n []          = []
drop n (x:xs)      = drop (n-1) xs

count :: Integer -> [Integer] -> Integer
count n [] = 0
count n (x:xs)
  | n == x = 1 + count n xs
  | otherwise = count n xs

msort :: [Integer] -> [Integer]
msort []  = []
msort [x] = [x]
msort xs  = merge (msort (take s2 xs)) (msort (drop s2 xs))
  where s2 = length xs `quot` 2

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

