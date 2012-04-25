module Guards where

import Prelude(Bool(..),otherwise)

data Nat  = Zero | Succ Nat

data K = A | B | C

even (Succ (Succ n)) = even n
even (Succ Zero)     = False
even Zero            = True

div3 (Succ (Succ (Succ n))) = div3 n
div3 Zero                   = True
div3 _                      = False

bar Zero           = C
bar x | even x     = A
      | div3 x     = B
      | otherwise  = C
