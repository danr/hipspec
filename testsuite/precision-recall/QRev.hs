{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module Main where

import Prelude hiding (reverse,(++))

import Data.Typeable

import HipSpec
import HipSpec.Prelude

data Nat = S Nat | Z
  deriving (Eq,Show,Typeable,Ord)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []     = []

qreverse :: [a] -> [a] -> [a]
qreverse []     acc = acc
qreverse (x:xs) acc = qreverse xs (x:acc)

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] intType
    , vars ["xs", "ys", "zs"] listType
    , fun0 "[]"       ([]       :: [A])
    , fun2 ":"        ((:)      :: A  -> [A] -> [A])
    , fun2 "++"       ((++)     :: [A] -> [A] -> [A])
    , fun1 "reverse"  (reverse  :: [A] -> [A])
    , fun2 "qreverse" (qreverse :: [A] -> [A] -> [A])
    ]
  where
    intType   = intType  :: A
    listType  = listType :: [A]