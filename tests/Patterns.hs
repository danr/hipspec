module Patterns where

data ABC = A | B | C

foo :: [a] -> [b] -> ABC
foo (_:_) _     = A
foo _     (_:_) = B
foo _     _     = C

