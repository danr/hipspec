module Lam where

import Prelude (print)

map f (x:xs) = f x : map f xs
map f []     = []

test x = map (\y -> (x,y))

-- main = print (test 1 "abc")