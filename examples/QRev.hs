module QRev where

import Prelude hiding ((++))
import HipSpec.Prelude
import List (List(..),(++),length)

rev :: List -> List
rev (Cons x xs) = rev xs ++ Cons x Nil
rev Nil         = Nil

qrev :: List -> List -> List
qrev Nil         ys = ys
qrev (Cons x xs) ys = qrev xs (Cons x ys)

