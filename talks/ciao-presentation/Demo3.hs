{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return,div)
import qualified Prelude as P
import Data.Typeable
import Test.QuickCheck hiding (Prop)
import Control.Applicative

import Hip.HipSpec

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

prop_assoc :: [a] -> [a] -> [a] -> Prop [a]
prop_assoc xs ys zs = xs ++ (ys ++ zs) =:= (xs ++ ys) ++ zs

prop_right_id :: [a] -> Prop [a]
prop_right_id xs = xs ++ [] =:= xs

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

type List = [Int]

main = hipSpec "Demo3.hs" conf 3
  where conf = describe "Lists"
                [ var "x"        intType
                , var "y"        intType
                , var "z"        intType
                , var "xs"       listType
                , var "ys"       listType
                , var "zs"       listType
                , con "[]"       ([]       :: List)
                , con ":"        ((:)      :: Int  -> List -> List)
                , con "++"       ((++)     :: List -> List -> List)
                , con "reverse"  (reverse  :: List -> List)
                , con "qreverse" (qreverse :: List -> List)
                , con "revacc"   (revacc   :: List -> List -> List)
                ]
                   where
                     intType   = undefined :: Int
                     listType  = undefined :: List

-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
