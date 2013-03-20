module Testing.Rotate where

import Prelude hiding (reverse,(++),length)

import HipSpec.Prelude

import Nat hiding (sig)
import List hiding (sig)

-- This version fails to compile
rotate :: Nat -> List -> List
rotate Z     xs          = xs
rotate _     Nil         = Nil
rotate (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

-- This version works
rotate' :: Nat -> List -> List
rotate' Z     xs          = xs
rotate' (S _) Nil         = Nil
rotate' (S n) (Cons x xs) = rotate n (xs ++ Cons x Nil)

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
    , fun2 "rotate'" rotate'
    ]

