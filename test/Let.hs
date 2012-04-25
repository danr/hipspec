module Let where

import Prelude ()

data Nat  = Zero | Succ Nat

f x = let z = Succ x in z

g x = let r z = Succ (Succ z) in r x

h x = let r x = Succ (Succ x) in r x