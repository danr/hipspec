module Vardep where

import Prelude()

data Tri = A | B | C

data Nat = Succ Nat | Zero

Zero   + y = y
Succ x + y = Succ (x + y)

g x y = case x + y of
           Succ _ -> C
           Zero -> case y of
                       Zero   -> A
                       Succ _ -> B
