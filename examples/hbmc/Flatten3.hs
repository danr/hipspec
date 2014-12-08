{-# LANGUAGE DeriveDataTypeable #-}
module Flatten3 where

import Data.Typeable (Typeable)
import List
import HipSpec
import Prelude hiding ((++))
import Control.Monad

data Tree a = B (Tree a) (Tree a) | Leaf a
  deriving (Typeable,Eq,Ord,Show)

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized arbTree
    where
      arbTree s = frequency
        [ (1,liftM Leaf arbitrary)
        , (s,liftM2 B (arbTree (s`div`2)) (arbTree (s`div`2)))
        ]

-- Koen's suggestion: pick up the commonly used names from the source code :)

flat1 :: Tree a -> [a]
flat1 (B l r)  = flat1 l ++ flat1 r
flat1 (Leaf a) = [a]

flat2 :: Tree a -> [a]
flat2 (B (B l r) q)  = flat2 (B l (B r q))
flat2 (B (Leaf x) r) = x : flat2 r
flat2 (Leaf x)       = [x]

flat3 :: [Tree a] -> [a]
flat3 []          = []
flat3 (Leaf x:xs) = x:flat3 xs
flat3 (B l r:xs)  = flat3 (l:r:xs)

prop_flat3 x  = flat3 [x] =:= flat2 x
nonsense1 x   = flat3 [x] =:= flat2 x ==> True =:= False
nonsense2 x   = flat3 [x,x] =:= flat2 x
nonsense3 x y = flat3 [y] =:= flat2 x
