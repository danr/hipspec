module Map where

import Prelude()

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs
