module Reverse where

import Prelude hiding (reverse,(++))
import HipSpec.Prelude
import List

reverse :: List -> List
reverse (Cons x xs) = reverse xs ++ Cons x Nil
reverse Nil         = Nil

revacc :: List -> List -> List
revacc Nil         ys = ys
revacc (Cons x xs) ys = revacc xs (Cons x ys)

qreverse :: List -> List
qreverse xs = revacc xs Nil

prop_morphism       :: List -> List -> Prop List
prop_morphism xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_involutary     :: List -> Prop List
prop_involutary xs  = reverse (reverse xs) =:= xs

prop_equal          :: List -> Prop List
prop_equal xs       = qreverse xs =:= reverse xs

sig =
    [ vars ["x", "y", "z"]    (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: List)
    , fun0 "Nil"      Nil
    , fun2 "Cons"     Cons
    , fun2 "++"       (++)
    , fun1 "reverse"  reverse
    , fun1 "qreverse" qreverse
    , fun2 "revacc"   revacc
    ]

