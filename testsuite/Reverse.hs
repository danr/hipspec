{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return,div)

import Data.Typeable

import Hip.HipSpec
import Hip.Prelude

{-# ANN (:) ":" #-}
{-# ANN [] "[]" #-}

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

main = hipSpec "Reverse.hs" conf 3
  where conf = describe "[Int]s"
                [ var "x"        intType
                , var "y"        intType
                , var "z"        intType
                , var "xs"       listType
                , var "ys"       listType
                , var "zs"       listType
                , con "[]"       ([]       :: [Int])
                , con ":"        ((:)      :: Int  -> [Int] -> [Int])
                , con "++"       ((++)     :: [Int] -> [Int] -> [Int])
                , con "reverse"  (reverse  :: [Int] -> [Int])
                , con "qreverse" (qreverse :: [Int] -> [Int])
                , con "revacc"   (revacc   :: [Int] -> [Int] -> [Int])
                ]
                   where
                     intType   = undefined :: Int
                     listType  = undefined :: [Int]

