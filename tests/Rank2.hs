{-# LANGUAGE Rank2Types #-}
module Rank2 where

f :: (forall a . a -> a -> a) -> (Bool,[Bool])
f g = (g True False,g [True] [False])

test = f (\ x y -> x)

