module Defaults where

data ABC = A | B | C

le A _ = True
le _ C = True
le B B = True
le _ _ = False

data U = S U | Z | R

m Z     _     = Z
m x     Z     = x
m R     x     = x
m _     R     = R
m (S x) (S y) = m x y

