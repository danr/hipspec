-- Properties come from QuickSpec
module Lists where

import HipPrelude
import Prelude (Int)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

point :: a -> [a]
point x = [x]

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ point x
reverse []     = []

reverse2 :: [a] -> [a]
reverse2 = revAcc []

revAcc :: [a] -> [a] -> [a]
revAcc acc []     = acc
revAcc acc (x:xs) = revAcc (x:acc) xs

prop_00 :: a -> [a] -> Prop [a]
prop_00 x xs = x:xs =:= revAcc xs (point x)

prop_01 :: [a] -> [a] -> Prop [a]
prop_01 xs ys = ys ++ xs =:= revAcc xs (reverse ys)

prop_02 :: [a] -> [a] -> Prop [a]
prop_02 xs ys = revAcc ys xs =:= reverse xs ++ ys

prop_03 :: [a] -> [a] -> Prop [a]
prop_03 xs ys = ys ++ xs =:= revAcc xs (reverse2 ys)

prop_04 :: [a] -> [a] -> Prop [a]
prop_04 xs ys = revAcc ys xs =:= reverse2 xs ++ ys

prop_05 :: [a] -> Prop [a]
prop_05 xs = reverse2 xs =:= reverse xs

prop_06 :: a -> Prop [a]
prop_06 x = x:[] =:= point x

prop_07 :: [a] -> Prop [a]
prop_07 xs = xs ++ [] =:= xs

prop_08 :: [a] -> Prop [a]
prop_08 xs = revAcc xs [] =:= xs

prop_09 :: [a] -> Prop [a]
prop_09 xs = [] ++ xs =:= xs

prop_10 :: [a] -> Prop [a]
prop_10 xs = revAcc [] xs =:= reverse xs

prop_11 :: [a] -> Prop [a]
prop_11 xs = revAcc [] xs =:= reverse2 xs

prop_12 :: a -> [a] -> [a] -> Prop [a]
prop_12 x xs ys = (x:xs) ++ ys =:= x:(xs ++ ys)

prop_13 :: [a] -> [a] -> [a] -> Prop [a]
prop_13 xs ys zs = (xs ++ ys) ++ zs =:= xs ++ (ys ++ zs)

prop_14 :: [a] -> [a] -> [a] -> Prop [a]
prop_14 xs ys zs = revAcc xs ys ++ zs =:= revAcc zs (revAcc ys xs)

prop_15 :: a -> [a] -> [a] -> Prop [a]
prop_15 x xs ys = revAcc (x:xs) ys =:= revAcc xs (x:ys)

prop_16 :: [a] -> [a] -> [a] -> Prop [a]
prop_16 xs ys zs = revAcc (revAcc xs ys) zs =:= revAcc xs (ys ++ zs)

main = do
  quickCheck (printTestCase "prop_00" (prop_00 :: Int -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_01" (prop_01 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_02" (prop_02 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_03" (prop_03 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_04" (prop_04 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_05" (prop_05 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_06" (prop_06 :: Int -> Prop [Int]))
  quickCheck (printTestCase "prop_07" (prop_07 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_08" (prop_08 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_09" (prop_09 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_10" (prop_10 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_11" (prop_11 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_12" (prop_12 :: Int -> [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_13" (prop_13 :: [Int] -> [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_14" (prop_14 :: [Int] -> [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_15" (prop_15 :: Int -> [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_16" (prop_16 :: [Int] -> [Int] -> [Int] -> Prop [Int]))
