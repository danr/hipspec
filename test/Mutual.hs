module Mutual where

import Prelude ()

data Nat = Succ Nat | Zero
data Bool = True | False

not True      = False
not False     = True

even (Succ x) = not (odd x)
even Zero     = True
odd (Succ x)  = not (even x)
odd Zero      = True