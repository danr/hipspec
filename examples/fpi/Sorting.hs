{-# LANGUAGE MagicHash #-}
module Sorting where

import Prelude hiding ((++),length)

length :: [Integer] -> Int
length [] = 0
length (_:xs) = 1 + length xs

{-
count :: Integer -> [Integer] -> Int
count n [] = 0
count n (x:xs)
  | n == x = 1 `plus` count n xs
  | otherwise = count n xs
  -}

plus :: Int -> Int -> Int
plus x y = x + y
    -- Dictionary unfoldings does not seem to be exported, so we use the prim version.. :(
    -- NOINLINE so it reaches QuickSpec with a type

sorted :: [Integer] -> Bool
sorted (x:y:xs)
  | x <= y    = sorted (y:xs)
  | otherwise = False
sorted _      = True

