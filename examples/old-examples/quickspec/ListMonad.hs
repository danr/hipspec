
{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
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

main = hipSpec "ListMonad.hs" conf 3
  where
    conf = describe "List Monad"
                [ var "x"        (undefined :: Int)
                , var "y"        (undefined :: Int)
                , var "z"        (undefined :: Int)
                , var "xs"       (undefined :: [Int])
                , var "ys"       (undefined :: [Int])
                , var "zs"       (undefined :: [Int])
                , var "xss"      (undefined :: [[Int]])
                , var "yss"      (undefined :: [[Int]])
                , var "zss"      (undefined :: [[Int]])
                , var "f"        (undefined :: Int     -> Int)
                , var "g"        (undefined :: Int     -> Int)
                , var "h"        (undefined :: Int     -> Int)
                , var "k"        (undefined :: Int     -> [Int])
                , var "i"        (undefined :: [Int]   -> Int)
                , var "j"        (undefined :: [Int]   -> [[Int]])
                , var "r"        (undefined :: [[Int]] -> [Int])
                , var "t"        (undefined :: Int     -> [[Int]])
                , con "id"       (id        :: [Int] -> [Int])
                , con "id"       (id        :: Int   -> Int)
               -- , con "."        ((.)       :: (Int   -> Int)   -> (Int   -> Int)   -> Int   -> Int)
               -- , con "."        ((.)       :: ([Int] -> [Int]) -> ([Int] -> [Int]) -> [Int] -> [Int])
                , con "[]"       ([]        :: [Int])
                , con "[]"       ([]        :: [[Int]])
                , con "point"    (point     :: Int   -> [Int])
                , con "point"    (point     :: [Int] -> [[Int]])
                , con ":"        ((:)       :: Int   -> [Int]   -> [Int])
                , con ":"        ((:)       :: [Int] -> [[Int]] -> [[Int]])
                , con "++"       ((++)      :: [Int]   -> [Int]   -> [Int])
                , con "++"       ((++)      :: [[Int]] -> [[Int]] -> [[Int]])
                , con "join"     (join      :: [[Int]] -> [Int])
                , con "join"     (join      :: [[[Int]]] -> [[Int]])
                , con ">>="      ((>>=)     :: [Int] -> (Int -> [Int]) -> [Int])
                , con ">>="      ((>>=)     :: [Int] -> (Int -> [[Int]]) -> [[Int]])
                , con "fmap"     (fmap      :: (Int -> Int) -> [Int] -> [Int])
                , con "fmap"     (fmap      :: (Int -> [Int]) -> [Int] -> [[Int]])
                ]

