{-# LANGUAGE TemplateHaskell #-}
module Main where

import Prelude hiding ((>>=),(++),fmap,id,(.))

import Data.Typeable

import HipSpec
import HipSpec.Prelude

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

(>>=) :: [a] -> (a -> [b]) -> [b]
(x:xs) >>= f = f x ++ (xs >>= f)
[]     >>= f = []

join :: [[a]] -> [a]
join ((x:xs):xss) = x:join (xs:xss)
join ([]:xss)     = join xss
join []           = []

fmap :: (a -> b) -> [a] -> [b]
fmap f []     = []
fmap f (x:xs) = f x : fmap f xs

prop_join_fmap_bind :: (a -> [b]) -> [a] -> Prop [b]
prop_join_fmap_bind f xs = join (fmap f xs) =:= xs >>= f

prop_assoc :: [a] -> (a -> [b]) -> (b -> [c]) -> Prop [c]
prop_assoc m f g = ((m >>= f) >>= g) =:= (m >>= (\x -> f x >>= g))

point :: a -> [a]
point x = [x]

f . g = \x -> f (g x)

id :: a -> a
id x = x

main = hipSpec $(fileName)
    [ pvars ["x","y","z"]       (undefined :: A)
    , pvars ["xs","ys","zs"]    (undefined :: [A])
    , pvars ["xss","yss","zss"] (undefined :: [[A]])
    , vars ["f","g","h"]        (undefined :: A -> A)
    , vars ["k"]                (undefined :: A     -> [A])
    , vars ["i"]                (undefined :: [A]   -> A)
    , vars ["j"]                (undefined :: [A]   -> [[A]])
    , vars ["r"]                (undefined :: [[A]] -> [A])
    , vars ["t"]                (undefined :: A     -> [[A]])
    , blind0 "id"               (id        :: [A] -> [A])
    , blind0 "id"               (id        :: A   -> A)
    , blind2 "."                ((.)       :: (A   -> A)   -> (A   -> A)   -> A   -> A)
    , blind2 "."                ((.)       :: ([A] -> [A]) -> ([A] -> [A]) -> [A] -> [A])
    , fun0 "[]"                 ([]        :: [A])
    , fun0 "[]"                 ([]        :: [[A]])
    , blind0 "point"            (point     :: A   -> [A])
    , fun1 "point"              (point     :: A   -> [A])
    , fun2 ":"                  ((:)       :: A   -> [A]   -> [A])
    , fun2 ":"                  ((:)       :: [A] -> [[A]] -> [[A]])
    , fun2 "++"                 ((++)      :: [A]   -> [A]   -> [A])
    , fun2 "++"                 ((++)      :: [[A]] -> [[A]] -> [[A]])
    , fun1 "join"               (join      :: [[A]] -> [A])
    , fun1 "join"               (join      :: [[[A]]] -> [[A]])
    , fun2 ">>="                ((>>=)     :: [A] -> (A -> [A]) -> [A])
    , fun2 ">>="                ((>>=)     :: [A] -> (A -> [[A]]) -> [[A]])
    , fun2 "fmap"               (fmap      :: (A -> A) -> [A] -> [A])
    , fun2 "fmap"               (fmap      :: (A -> [A]) -> [A] -> [[A]])
    ]

