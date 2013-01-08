module Main where

import Test.QuickSpec

-- This finds the weirdest properties, like
-- zipWith k xs ys = zipWith k ys xs
listFunctions = describe "ListFunctions"
                [ var "xs" listType
                , var "ys" listType
                , var "zs" listType
                , con "[]"      ([]      :: [Int])
                , con ":"       ((:)     :: Int -> [Int] -> [Int])
                , con "++"      ((++)    :: [Int] -> [Int] -> [Int])
                , con "map"     (map     :: (Int -> Int) -> [Int] -> [Int])
                , con "zipWith" (zipWith :: (Int -> Int -> Int) -> [Int] -> [Int] -> [Int])
                , var "f" unOpType
                , var "g" unOpType
                , var "k" binOpType
                , var "h" binOpType
                ]
  where
    listType  = undefined :: [Int]
    unOpType  = undefined :: Int -> Int
    binOpType = undefined :: Int -> Int -> Int

main = quickSpecDepth listFunctions 3
