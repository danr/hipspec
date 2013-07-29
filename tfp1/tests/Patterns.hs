module Patterns where

data ABC = A | B | C

foo :: [a] -> [b] -> ABC
foo (_:_) _     = A
foo _     (_:_) = B
foo _     _     = C

-- This function makes a fail function
foofail :: [a] -> [b] -> ABC
foofail (_:_) []    = A
foofail xs    (_:_) = B
foofail xs    ys    = C

