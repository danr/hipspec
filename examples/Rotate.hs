module Rotate where

import Prelude hiding ((++),length)

import HipSpec.Prelude

import Nat (Nat(..))
import List (List(..),(++),length)

rotate :: Nat -> List -> List
rotate Z     xs          = xs
rotate (S _) Nil         = Nil
rotate (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

-- T32 from productive use of failure
prop_T32 :: List -> Prop List
prop_T32 xs = rotate (length xs) xs =:= xs

sig =
    [ vars ["x", "y", "z"]    (undefined :: A)
    , vars ["n", "m", "o"]    (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: List)
    , fun0 "Z"      Z
    , fun1 "S"      S
    , fun0 "Nil"    Nil
    , fun2 "Cons"   Cons
    , fun1 "length" length
    , fun2 "++"     (++)
    , fun2 "rotate" rotate
    ]

