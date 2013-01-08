module Main where

import Test.QuickSpec

-- Desired property : map (f . g) xs == map f (map g xs), not found

mapCompose = describe "MapCompose"
                [ var "xs"  listType
                , con "map" (map :: (Int -> Int) -> [Int] -> [Int])
                , con "."   ((.) :: (Int -> Int) -> (Int -> Int) -> Int -> Int)
                , con "f"   unOpType
                , con "g"   unOpType
                ]
  where
    listType  = undefined :: [Int]
    unOpType  = undefined :: Int -> Int

main = quickSpecDepth mapCompose 7
