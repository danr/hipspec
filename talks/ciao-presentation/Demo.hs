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

main = hipSpec "Demo.hs" (describe "" []) 3



































-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
