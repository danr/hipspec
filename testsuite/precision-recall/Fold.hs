{-# LANGUAGE DeriveDataTypeable,TemplateHaskell,GeneralizedNewtypeDeriving #-}
module Main where

import Prelude hiding ((++),foldl,foldr)

import Data.Typeable

import HipSpec
import HipSpec.Prelude

newtype B = B Int deriving (Eq, Ord, Typeable, Arbitrary, CoArbitrary, Show)

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
    , vars ["e", "e'", "e''"] stateType
    , vars ["xs", "ys", "zs"] listType
    , vars ["f", "g"] (undefined :: B -> A -> B)
    , vars ["f", "g"] (undefined :: A -> B -> B)
    , fun0 "[]"       ([]       :: [A])
    , fun2 ":"        ((:)      :: A  -> [A] -> [A])
    , fun2 "++"       ((++)     :: [A] -> [A] -> [A])
    , fun3 "foldl"    (foldl    :: (B -> A -> B) -> B -> [A] -> B)
    , fun3 "foldr"    (foldr    :: (A -> B -> B) -> B -> [A] -> B)
    , observer2 (flip ($) :: A -> (A -> A) -> A)
    ]
  where
    intType   = intType   :: A
    stateType = stateType :: B
    listType  = listType  :: [A]
