{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module Main where

import Prelude hiding (reverse,(++),map)

import Data.Typeable

import HipSpec
import HipSpec.Prelude

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []     = []

map :: (a -> a) -> [a] -> [a]
map f [] = []
map f (x:xs) = f x:map f xs

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] intType
    , vars ["xs", "ys", "zs"] listType
    , vars ["f", "g"] (undefined :: A -> A)
    , fun0 "[]"       ([]       :: [A])
    , fun2 ":"        ((:)      :: A  -> [A] -> [A])
    , fun2 "++"       ((++)     :: [A] -> [A] -> [A])
    , fun1 "reverse"  (reverse  :: [A] -> [A])
    , fun2 "map"      (map      :: (A -> A) -> [A] -> [A])
    , fun2 "$" (($) :: (A -> A) -> A -> A)
    , observer2 (flip ($) :: A -> (A -> A) -> A)
    ]
  where
    intType   = intType  :: A
    listType  = listType :: [A]