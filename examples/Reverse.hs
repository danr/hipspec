module Reverse where

import Prelude hiding (reverse,(++))
import HipSpec.Prelude
import List (List(..),(++),length)

reverse :: List -> List
reverse (Cons x xs) = reverse xs ++ Cons x Nil
reverse Nil         = Nil

revacc :: List -> List -> List
revacc Nil         ys = ys
revacc (Cons x xs) ys = revacc xs (Cons x ys)

qreverse :: List -> List
qreverse xs = revacc xs Nil

prop_equal          :: List -> Prop List
prop_equal xs       = qreverse xs =:= reverse xs

