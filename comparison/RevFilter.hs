{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable #-}

module Main where

import Prelude (Bool(..),error,toEnum,fromEnum,pred,succ,sqrt,round,Int
               ,Enum,Eq,Ord,Show,return,(.),undefined)
import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Data.Typeable

main = hipSpec "RevFilter.hs" conf 3
  where conf = describe "Nats"
               [ var "x"         elemType
               , var "y"         elemType
               , var "z"         elemType
               , var "xs"        listType
               , var "ys"        listType
               , var "zs"        listType
               , var "p"         (undefined :: Int -> Bool)
               , con "[]"        ([]        :: [Int])
               , con ":"         ((:)       :: Int  -> [Int] -> [Int])
               , con "++"        ((++)      :: [Int] -> [Int] -> [Int])
               , con "filter"    (filter    :: (Int -> Bool) -> [Int] -> [Int])
               , con "rev"       (rev       :: [Int] -> [Int])
               ]
           where
             elemType  = (error "Elem type" :: Int)
             listType = (error "List type" :: [Int])


type Prop a = a

infix 0 =:=

(=:=) :: a -> a -> Prop a
(=:=) = (=:=)

proveBool :: Bool -> Prop Bool
proveBool = (=:= True)

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
     True  -> x : filter p xs
     _     -> filter p xs


prop_73 :: (a -> Bool) -> [a] -> Prop [a]
prop_73 p xs = (rev (filter p xs) =:= filter p (rev xs))

