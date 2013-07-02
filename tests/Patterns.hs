module Patterns where

data ABC = A | B | C

{-
foo :: [a] -> [b] -> ABC
foo (_:_) _     = A
foo _     (_:_) = B
foo _     _     = C
-}

foofail :: [a] -> [b] -> ABC
foofail (_:_) []    = A
foofail _     (_:_) = B
foofail _     _     = C

