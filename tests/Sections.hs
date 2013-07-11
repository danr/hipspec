module Sections where

import Prelude()

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

inits    :: [a] -> [[a]]
inits xs =  [] : case xs of
                    []      -> []
                    x : xs' -> map (x:) (inits xs')

singletons = map (:[])

