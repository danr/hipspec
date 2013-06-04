module Rotate where

import Prelude hiding ((++),length)

import HipSpec.Prelude

import Nat (Nat(..))
import List (List(..),(++),length)

rotate :: Nat -> List -> List
rotate Z     xs          = xs
rotate (S _) Nil         = Nil
rotate (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

prop_rotate :: List -> Prop List
prop_rotate xs = rotate (length xs) xs =:= xs

