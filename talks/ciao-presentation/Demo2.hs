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

main = hipSpec "Demo2.hs" (describe "" []) 3


























-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
