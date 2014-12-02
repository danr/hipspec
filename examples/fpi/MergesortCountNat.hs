{-# LANGUAGE DeriveDataTypeable #-}
module Mergesort where

import Prelude hiding ((++),uncurry,(+))
import HipSpec
import List ((++))
import Test.QuickCheck hiding ((==>))
import GHC.Types
import Data.Typeable
import Nat

count :: Integer -> [Integer] -> Nat
count n [] = Z
count n (x:xs)
  | n == x = S Z + (count n xs)
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

-- prop_1_merge_sorted xs ys = sorted xs =:= True ==> sorted ys =:= True ==> sorted (merge xs ys) =:= True

-- prop_2_msort_sorted xs = sorted (msort xs) =:= True

-- These four are really sufficient, but the last lemma does not get triggered in Z3 (nor CVC4)
{-
prop_31_count_flip xs ys x = count x (xs ++ ys) =:= count x (ys ++ xs)

prop_32_count_lr x xs = count x (evens xs ++ odds xs) =:= count x xs

prop_33_count_merge xs ys x = count x (xs ++ ys) =:= count x (merge xs ys)

prop_34_count_congl x xs ys zs = count x xs =:= count x ys ==> count x (xs ++ zs) =:= count x (ys ++ zs)

prop_34_count_cong_2 x xs ys zs ws =
    count x xs =:= count x ys ==>
    count x zs =:= count x ws ==>
    count x (xs ++ zs) =:= count x (ys ++ ws)
-}

{-
prop_3_count_lr_p x xs = count x (evens xs) + count x (odds xs) =:= count x xs

prop_4_count_merge xs ys x = count x xs + count x ys =:= count x (merge xs ys)
-}

prop_5_msort_tperm xs x = count x xs =:= count x (msort xs)

{-
-- these are the proved ones from
-- hipspec Mergesort.hs -f --plain --induction --z3 --unarysize=1 --termsize=7 --extra-trans=++
--pqs_1 xs = xs ++ [] =:= xs
--pqs_2 xs ys zs = (xs ++ ys) ++ zs =:= xs ++ (ys ++ zs)
pqs_3 i is js = count i (is ++ js) =:= count i (js ++ is)
--pqs_4 i is js = count i (merge is js) =:= count i (is ++ js)
--pqs_5 i is js ks = count i (is ++ (js ++ ks)) =:= count i (is ++ (ks ++ js))
--pqs_6 i is js ks = count i (is ++ merge js ks) =:= count i (is ++ (js ++ ks))
pqs_7 i is js = plus (count i is) (count i js) =:= count i (is ++ js)
pqs_8 i is = count i (evens is ++ odds is) =:= count i is
-- They seem to be too many to be able to prove count correctness
-}
