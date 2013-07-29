module Partition where

import Prelude (Bool(..))

(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

data Pair a b = Pair a b

partition :: (a -> Bool) -> [a] -> Pair [a] [a]
partition p []  = Pair [] []
partition p (x:xs)
    | p x  = Pair (x:ys) zs
    | True = Pair ys (x:zs)
  where
    Pair ys zs = partition p xs

qsort :: (a -> a -> Bool) -> [a] -> [a]
qsort (<) [] = []
qsort (<) (x:xs) = qsort (<) ys ++ [x] ++ qsort (<) zs
  where Pair ys zs = partition (< x) xs


