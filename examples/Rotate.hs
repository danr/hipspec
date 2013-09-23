module Rotate where

import Prelude hiding ((++),length)

import HipSpec

import Nat (Nat(..),(+))
import List ((++),length)

rotate :: Nat -> [a] -> [a]
rotate Z     xs     = xs
rotate _     []     = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

prop_rotate :: [a] -> Prop [a]
prop_rotate xs = rotate (length xs) xs =:= xs

