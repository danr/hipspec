module Count where

import Prelude hiding ((++))
import HipSpec

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

count :: Eq a => a -> [a] -> Int
count _ [] = 0
count x (y:ys)
    | x == y = 1 + count x ys
    | otherwise = count x ys

prop_count_append x xs ys = count x xs + count x ys =:= count x (xs ++ ys)

