{-# LANGUAGE DeriveDataTypeable,TypeOperators #-}
module Mirror where

import Data.Typeable (Typeable)
import List
import Reverse (rev)
import HipSpec
import Prelude hiding ((++),map)
import Control.Monad
import Test.QuickCheck.Modifiers
import QuickSpec
import QuickSpec.Type
import QuickSpec.Signature

data Tree a = Br [Tree a] | Leaf a
  deriving (Typeable,Eq,Ord,Show)

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized arbTree
    where
      arbTree s = do
        frequency
            [ (1,liftM Leaf arbitrary)
            , (s,liftM Br (arbList (s`div`2)))
            ]

      arbList s = do
        n <- choose (0,s)
        replicateM n (arbTree s)

mirror :: Tree a -> Tree a
mirror (Leaf x) = Leaf x
mirror (Br ts)  = Br (rev (map mirror ts))

mirror2 :: Tree a -> Tree a
mirror2 (Leaf x) = Leaf x
mirror2 (Br ts)  = Br (map mirror2 (rev ts))

prop_equal t = mirror t =:= mirror2 t
