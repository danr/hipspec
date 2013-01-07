module Main where

import Test.QuickSpec

-- Need to instantiate flip and foldl quite precise
-- Desired property foldl (flip (:)) [] xs == reverse xs, found!
reverseSpec = describe "Reverse"
                [ var "xs" listType
                , con "[]"      ([]      :: [Int])
                , con ":"       ((:)     :: Int -> [Int] -> [Int])
                , con "flip"    (flip    :: (Int -> [Int] -> [Int]) -> [Int] -> Int -> [Int])
                , con "foldl"   (foldl   :: ([Int] -> Int -> [Int]) -> [Int] -> [Int] -> [Int])
                , con "reverse" (reverse :: [Int] -> [Int])
                ]
  where
    listType  = undefined :: [Int]

main = quickSpecDepth reverseSpec 3
