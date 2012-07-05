{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Main where

import Prelude hiding (reverse,(++))

import Data.Typeable

import Hip.HipSpec
import Hip.Prelude

{-# ANN (++) "++" #-}
(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

{-# ANN reverse "reverse" #-}
reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []     = []

{-# ANN revacc "revacc" #-}
revacc :: [a] -> [a] -> [a]
revacc []     acc = acc
revacc (x:xs) acc = revacc xs (x:acc)

{-# ANN qreverse "qreverse" #-}
qreverse :: [a] -> [a]
qreverse xs = revacc xs []

prop_morphism       :: [a] -> [a] -> Prop [a]
prop_morphism xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_involutary     :: [a] -> Prop [a]
prop_involutary xs  = reverse (reverse xs) =:= xs

prop_equal          :: [a] -> Prop [a]
prop_equal xs       = qreverse xs =:= reverse xs

main = hipSpec "Reverse.hs" conf
  where conf = [ vars ["x", "y", "z"] intType
               , vars ["xs", "ys", "zs"] listType
               , fun0 "[]"       ([]       :: [Int])
               , fun2 ":"        ((:)      :: Int  -> [Int] -> [Int])
               , fun2 "++"       ((++)     :: [Int] -> [Int] -> [Int])
               , fun1 "reverse"  (reverse  :: [Int] -> [Int])
               , fun1 "qreverse" (qreverse :: [Int] -> [Int])
               , fun2 "revacc"   (revacc   :: [Int] -> [Int] -> [Int])
               ]
                   where
                     intType   = intType  :: Int
                     listType  = listType :: [Int]

