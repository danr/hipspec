{-# LANGUAGE TemplateHaskell #-}
module Main where

import Prelude hiding ((>>=),(++),map,id,(.), repeat, iterate, head, tail)

import Data.Typeable

import HipSpec
import HipSpec.Prelude
import Test.QuickSpec.Signature

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

main = hipSpec $(fileName)
    [ pvars ["x","y","z"]       (undefined :: A)
    , pvars ["xs","ys","zs"]    (undefined :: [A])
    , vars ["f","g"]                (undefined :: A -> A)
    , blind0 "id"               (id        :: A   -> A)
    , background (fun0 "[]"                 ([]        :: [A]))
    , background (fun2 ":" ((:) :: A -> [A] -> [A]))
    , fun2 "++"                 ((++)      :: [A]   -> [A]   -> [A])
    , fun2 "iterate" (iterate :: (A -> A) -> A -> [A])
    , fun1 "repeat" (repeat :: A -> [A])
    , fun1 "cycle" (cycle :: [A] -> [A])
    , fun1 "head" (head :: [A] -> A)
    , fun1 "tail" (tail :: [A] -> [A])
    , fun2 "map"               (map      :: (A -> A) -> [A] -> [A])
    , withQuickCheckSize 10
    ]

