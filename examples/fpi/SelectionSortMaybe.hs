module SelectionSort where

import Prelude hiding ((++),minimum,min,length)
import Data.Maybe
import HipSpec
import List ((++))
import Test.QuickCheck hiding ((==>))
import GHC.Types
import Data.Typeable
import Sorting

delete :: Integer -> [Integer] -> [Integer]
delete x (y:ys)
    | x == y    = ys
    | otherwise = y:delete x ys
delete _ [] = []

mmap :: (a -> b) -> Maybe a -> Maybe b
mmap f (Just x) = Just (f x)
mmap _ Nothing  = Nothing

min :: Integer -> Integer -> Integer
min x y | x < y     = x
        | otherwise = y

minimum :: [Integer] -> Maybe Integer
minimum []     = Nothing
minimum [x]    = Just x
minimum (x:xs) = mmap (min x) (minimum xs)

ssort :: [Integer] -> [Integer]
ssort [] = []
ssort xs = case minimum xs of
    Nothing -> []
    Just m  -> m : ssort (delete m xs)

prop_ssort_sorted xs = sorted (ssort xs) =:= True

prop_ssort_count n xs = count n xs =:= count n (ssort xs)

prop_ssort_length xs = length xs =:= length (ssort xs)

length :: [Integer] -> Int
length [] = 0
length (_:xs) = 1 `plus` length xs

count :: Integer -> [Integer] -> Int
count n [] = 0
count n (x:xs)
  | n == x = 1 `plus` count n xs
  | otherwise = count n xs

{-# NOINLINE plus #-}
plus :: Int -> Int -> Int
plus x y = x + y

sorted :: [Integer] -> Bool
sorted (x:y:xs)
  | x <= y    = sorted (y:xs)
  | otherwise = False
sorted _      = True

