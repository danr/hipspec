{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, ScopedTypeVariables #-}
module Main where

import Prelude hiding ((>>=),(++),fmap,id,(.))

import Data.Typeable

import Hip.HipSpec
import Hip.Prelude

{-# ANN (++) "++" #-}
(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

{-# ANN (>>=) ">>=" #-}
(>>=) :: [a] -> (a -> [b]) -> [b]
(x:xs) >>= f = f x ++ (xs >>= f)
[]     >>= f = []

{-# ANN join "join" #-}
join :: [[a]] -> [a]
join ((x:xs):xss) = x:join (xs:xss)
join ([]:xss)     = join xss
join []           = []

{-# ANN fmap "fmap" #-}
fmap :: (a -> b) -> [a] -> [b]
fmap f []     = []
fmap f (x:xs) = f x : fmap f xs

prop_join_fmap_bind :: (a -> [b]) -> [a] -> Prop [b]
prop_join_fmap_bind f xs = join (fmap f xs) =:= xs >>= f

prop_assoc :: [a] -> (a -> [b]) -> (b -> [c]) -> Prop [c]
prop_assoc m f g = ((m >>= f) >>= g) =:= (m >>= (\x -> f x >>= g))

{-# ANN point "point" #-}
point :: a -> [a]
point x = [x]

{-# ANN (.) "." #-}
f . g = \x -> f (g x)

{-# ANN id "id" #-}
id :: a -> a
id x = x

main = hipSpec "ListMonad.hs" conf
  where
    conf = [ vars ["x","y","z"]       (undefined :: Int)
           , vars ["xs","ys","zs"]    (undefined :: [Int])
           , vars ["xss","yss","zss"] (undefined :: [[Int]])
           , vars ["f","g","h"]       (undefined :: Int -> Int)
           , vars ["k"]               (undefined :: Int     -> [Int])
           , vars ["i"]               (undefined :: [Int]   -> Int)
           , vars ["j"]               (undefined :: [Int]   -> [[Int]])
           , vars ["r"]               (undefined :: [[Int]] -> [Int])
           , vars ["t"]               (undefined :: Int     -> [[Int]])
           , blind0 "id"              (id        :: [Int] -> [Int])
           , blind0 "id"              (id        :: Int   -> Int)
           , blind2 "."               ((.)       :: (Int   -> Int)   -> (Int   -> Int)   -> Int   -> Int)
           , blind2 "."               ((.)       :: ([Int] -> [Int]) -> ([Int] -> [Int]) -> [Int] -> [Int])
           , fun0 "[]"                ([]        :: [Int])
           , fun0 "[]"                ([]        :: [[Int]])
           , blind0 "point"           (point     :: Int   -> [Int])
           , fun1 "point"             (point     :: Int   -> [Int])
           , fun2 ":"                 ((:)       :: Int   -> [Int]   -> [Int])
           , fun2 ":"                 ((:)       :: [Int] -> [[Int]] -> [[Int]])
           , fun2 "++"                ((++)      :: [Int]   -> [Int]   -> [Int])
           , fun2 "++"                ((++)      :: [[Int]] -> [[Int]] -> [[Int]])
           , fun1 "join"              (join      :: [[Int]] -> [Int])
           , fun1 "join"              (join      :: [[[Int]]] -> [[Int]])
           , fun2 ">>="               ((>>=)     :: [Int] -> (Int -> [Int]) -> [Int])
           , fun2 ">>="               ((>>=)     :: [Int] -> (Int -> [[Int]]) -> [[Int]])
           , fun2 "fmap"              (fmap      :: (Int -> Int) -> [Int] -> [Int])
           , fun2 "fmap"              (fmap      :: (Int -> [Int]) -> [Int] -> [[Int]])
           , observer2 $ (($) :: (Int -> Int) -> (Int -> Int))
           , observer2 $ (($) :: ([Int] -> Int) -> ([Int] -> Int))
           , observer2 $ (($) :: (Int -> [Int]) -> (Int -> [Int]))
           , observer2 $ (($) :: ([Int] -> [Int]) -> ([Int] -> [Int]))
           ]

