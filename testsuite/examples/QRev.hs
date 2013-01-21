{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module Main where

import Prelude hiding (rev,(++))

import Data.Typeable

import HipSpec
import HipSpec.Prelude

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

rev :: [a] -> [a]
rev (x:xs) = rev xs ++ [x]
rev []     = []

qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

prop_equal :: [a] -> Prop [a]
prop_equal xs = qrev xs [] =:= rev xs

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] intType
    , vars ["xs", "ys", "zs"] listType
    , fun0 "[]"   ([]   :: [A])
    , fun2 ":"    ((:)  :: A  -> [A] -> [A])
    , fun2 "++"   ((++) :: [A] -> [A] -> [A])
    , fun1 "rev"  (rev  :: [A] -> [A])
    , fun2 "qrev" (qrev :: [A] -> [A] -> [A])
    ]
  where
    intType   = intType  :: A
    listType  = listType :: [A]

