{-# LANGUAGE DeriveDataTypeable #-}
module Int where

import Prelude hiding (length,take,drop,(++),replicate)
import HipSpec

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

take :: Int -> [a] -> [a]
take n xs | n <= 0 = []
take n []     = []
take n (x:xs) = x:take (n-1) xs

drop :: Int -> [a] -> [a]
drop n xs | n <= 0 = xs
drop n []          = []
drop n (x:xs)      = drop (n-1) xs

replicate :: Int -> a -> [a]
replicate n x | n <= 0 = []
replicate n x          = x : replicate (n-1) x


rotate :: Int -> [a] -> [a]
rotate n xs | n <= 0 = xs
rotate _ []          = []
rotate n (x:xs)      = rotate (n-1) (xs ++ [x])

rot_len xs = rotate  (length xs) xs =:= xs

len_nonneg xs = length xs >= 0 =:= True

take_drop n xs = take n xs ++ drop n xs =:= xs

rot_repl x n y = rotate x (replicate n y) =:= replicate n y
