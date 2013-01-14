{-# LANGUAGE DeriveDataTypeable,TemplateHaskell,GeneralizedNewtypeDeriving #-}
module Main where

import Prelude hiding ((++),foldl,foldr)

import Data.Typeable

import HipSpec
import HipSpec.Prelude

app :: a -> a
app x = x

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

foldl :: (a -> b -> a) -> a -> [b] -> a
foldl op e [] = e
foldl op e (x:xs) = foldl op (op e x) xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr op e [] = e
foldr op e (x:xs) = op x (foldr op e xs)

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] intType
    , vars ["xs", "ys", "zs"] listType
    , vars ["f", "g"] (undefined :: A -> A -> A)
    , fun0 "[]"       ([]       :: [A])
    , fun2 ":"        ((:)      :: A  -> [A] -> [A])
    , fun2 "++"       ((++)     :: [A] -> [A] -> [A])
    , fun3 "foldl"    (foldl    :: (A -> A -> A) -> A -> [A] -> A)
    , fun3 "foldr"    (foldr    :: (A -> A -> A) -> A -> [A] -> A)
    ]
  where
    intType   = intType   :: A
    listType  = listType  :: [A]
