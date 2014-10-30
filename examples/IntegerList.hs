{-# LANGUAGE DeriveDataTypeable #-}
module Integer where

import Prelude hiding (length,take,drop,(++),replicate)
import HipSpec

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

length :: [a] -> Integer
length []     = 0
length (_:xs) = 1 + length xs

take :: Integer -> [a] -> [a]
take n xs | n <= 0 = []
take n []     = []
take n (x:xs) = x:take (n-1) xs

len_nonneg xs = length xs >= 0 =:= True

takeprop xs = take (length xs) xs =:= xs

drop :: Integer -> [a] -> [a]
drop n xs | n <= 0 = xs
drop n []          = []
drop n (x:xs)      = drop (n-1) xs

replicate :: Integer -> a -> [a]
replicate n x | n <= 0 = []
replicate n x          = x : replicate (n-1) x

-- lr n x = length (replicate n x) =:= min n 0
lr n x = n >= 0 =:= True ==> length (replicate n x) =:= n


rotate :: Integer -> [a] -> [a]
rotate n xs | n <= 0 = xs
rotate _ []          = []
rotate n (x:xs)      = rotate (n-1) (xs ++ [x])

rot_len xs = rotate  (length xs) xs =:= xs


take_drop n xs = take n xs ++ drop n xs =:= xs

rot_repl x n y = rotate x (replicate n y) =:= replicate n y
