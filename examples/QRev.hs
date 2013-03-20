module QRev where

import Prelude hiding ((++))
import HipSpec.Prelude
import List hiding (sig)

rev :: List -> List
rev (Cons x xs) = rev xs ++ Cons x Nil
rev Nil         = Nil

qrev :: List -> List -> List
qrev Nil         ys = ys
qrev (Cons x xs) ys = qrev xs (Cons x ys)

{-
prop_equal :: List -> Prop List
prop_equal xs = qrev xs Nil =:= rev xs
-}

sig =
    [ vars ["x", "y", "z"]    (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: List)
    , fun0 "Nil"    Nil
    , fun2 "Cons"   Cons
    , fun2 "++"     (++)
    , fun1 "rev"    rev
    , fun2 "qrev"   qrev
    ]

