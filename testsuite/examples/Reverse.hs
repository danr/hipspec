{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module Main where

import Prelude hiding (reverse,(++))

import Data.Typeable

import HipSpec
import HipSpec.Prelude

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []     = []

revacc :: [a] -> [a] -> [a]
revacc []     acc = acc
revacc (x:xs) acc = revacc xs (x:acc)

qreverse :: [a] -> [a]
qreverse xs = revacc xs []

prop_morphism       :: [a] -> [a] -> Prop [a]
prop_morphism xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_involutary     :: [a] -> Prop [a]
prop_involutary xs  = reverse (reverse xs) =:= xs

prop_equal          :: [a] -> Prop [a]
prop_equal xs       = qreverse xs =:= reverse xs

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] intType
    , vars ["xs", "ys", "zs"] listType
    , fun0 "[]"       ([]       :: [A])
    , fun2 ":"        ((:)      :: A  -> [A] -> [A])
    , fun2 "++"       ((++)     :: [A] -> [A] -> [A])
    , fun1 "reverse"  (reverse  :: [A] -> [A])
    , fun1 "qreverse" (qreverse :: [A] -> [A])
    , fun2 "revacc"   (revacc   :: [A] -> [A] -> [A])
    ]
  where
    intType   = intType  :: A
    listType  = listType :: [A]

