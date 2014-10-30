{-# LANGUAGE DeriveDataTypeable #-}
module Int where

import Prelude hiding (length,take,drop,(++))
import HipSpec

{-
(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

len_morph xs ys = length (xs ++ ys) =:= length xs + length ys
-}

length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

{-
take :: Int -> [a] -> [a]
take 0 xs     = []
take n []     = []
take n (x:xs) = x:take (n-1) xs

take_len xs = take (length xs) xs =:= xs
-}

drop :: Int -> [a] -> [a]
drop n xs | n <= 0 = xs
drop n []          = []
drop n (x:xs)      = drop (n-1) xs

drop_len xs = drop (length xs) xs =:= []

{-
take_drop n xs = take n xs ++ drop n xs =:= xs
-}


