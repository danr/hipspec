{-# LANGUAGE ScopedTypeVariables #-}
module PolyLet where

f :: forall a . a -> ([a],[a])
f x =
    let g :: forall b . b -> [a]
        g _ = [x]
    in  (g x,g [True])

-- Recursive variant that doesn't disappear in optimisation,
-- and x occurs free in g
frec :: forall a . a -> ([a],[a])
frec x =
    let g :: forall b . [b] -> [a]
        g []     = []
        g (_:xs) = x:g xs
    in  (g [x,x,x],g [True,False])
