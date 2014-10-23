{-# LANGUAGE TemplateHaskell #-}
module Main where

import Prelude hiding ((>>=),(++),map,id,(.), repeat, iterate, head, tail)

import Data.Typeable

import HipSpec
import HipSpec.Prelude
import QuickSpec.Signature

id :: a -> a
id x = x

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

head (x:xs) = x
tail (x:xs) = xs

repeat x = x:repeat x
iterate f x = x:iterate f (f x)

map_iter f x = map f (iterate f x) =:= iterate f (f x)

main = hipSpec $(fileName) ([] :: [Sig])

