module SK where

s :: (a -> b -> c) -> (a -> b) -> a -> c
s f g x = f x (g x)

k :: a -> b -> a
k x y = x

sant = True

i :: a -> a
i = s k (k :: b -> b -> b)

