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
msort xs  = merge (msort (evens xs)) (msort (odds xs))

evens :: [Integer] -> [Integer]
evens []      = []
evens (x:rs)  = x:odds rs

odds :: [Integer] -> [Integer]
odds []     = []
odds (x:rs) = evens rs

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

prop_1_merge_sorted xs ys = sorted xs =:= True ==> sorted ys =:= True ==> sorted (merge xs ys) =:= True

prop_2_msort_sorted xs = sorted (msort xs) =:= True

{-
-- These four are really sufficient, but the last lemma does not get triggered in Z3 (nor CVC4)
prop_count_flip xs ys x = count x (xs ++ ys) =:= count x (ys ++ xs)

prop_count_lr x xs = count x (evens xs ++ odds xs) =:= count x xs

prop_count_merge xs ys x = count x (xs ++ ys) =:= count x (merge xs ys)

prop_count_inj_l x xs ys zs = count x xs =:= count x ys ==> count x (xs ++ zs) =:= count x (ys ++ zs)
-}

prop_3_count_lr_p x xs = count x (evens xs) + count x (odds xs) =:= count x xs

prop_4_count_merge xs ys x = count x xs + count x ys =:= count x (merge xs ys)

prop_5_msort_tperm xs x = count x xs =:= count x (msort xs)

