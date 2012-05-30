module Trees where

import AutoPrelude
import Prelude ()

data Tree a = Fork (Tree a) (Tree a) | Leaf a

return :: a -> Tree a
return = Leaf

(>>=) :: Tree a -> (a -> Tree b) -> Tree b
Fork u v >>= f = Fork (u >>= f) (v >>= f)
Leaf x   >>= f = f x

prop_return_right t  = t >>= return     =:=  t

prop_return_left f x = return x >>= f   =:=  f x

prop_assoc t f g     = (t >>= f) >>= g  =:=  t >>= (\x -> f x >>= g)

prop_return_right :: Tree a -> Prop (Tree a)
prop_return_left :: (a -> Tree b) -> a -> Prop (Tree b)
prop_assoc :: Tree a -> (a -> Tree b) -> (b -> Tree c) -> Prop (Tree c)

