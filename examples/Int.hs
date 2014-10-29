{-# LANGUAGE DeriveDataTypeable #-}
module Int where

import Prelude hiding (length,take,drop,(++))
import HipSpec

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

len_morph xs ys = length (xs ++ ys) =:= length xs + length ys

{-
take :: Int -> [a] -> [a]
take n xs | n <= 0 = []
take n []          = []
take n (x:xs)      = x:take (n-1) xs

drop :: Int -> [a] -> [a]
drop n xs | n <= 0 = xs
drop n (x:xs)      = drop (n-1) xs

--take_drop n xs = take n xs ++ drop n xs =:= xs
-}


