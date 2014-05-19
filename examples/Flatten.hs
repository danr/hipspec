{-# LANGUAGE DeriveDataTypeable #-}
module Flatten where

import Data.Typeable (Typeable)
import List
import HipSpec
import Prelude hiding ((++))
import Control.Monad

data Tree a = B (Tree a) a (Tree a) | Leaf
  deriving (Typeable,Eq,Ord,Show)

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized arbTree
    where
      arbTree s = frequency
        [ (1,return Leaf)
        , (s,liftM3 B (arbTree (s`div`2)) arbitrary (arbTree (s`div`2)))
        ]

instance Names (Tree a) where
    names _ = ["p","q","r"]

flat1 :: Tree a -> [a]
flat1 (B l x r) = flat1 l ++ [x] ++ flat1 r
flat1 Leaf      = []

flat2 :: Tree a -> [a]
flat2 (B (B l x r) y q) = flat2 (B l x (B r y q))
flat2 (B Leaf x r)      = x : flat2 r
flat2 Leaf              = []

