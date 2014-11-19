module Simple where

data K = K1 K | K2 K | K3 K

g,h :: K -> K
g x = K1 x
h x = K2 x

f :: K -> K
f x = case f x of
    K1 a -> g (f a)
    K2 b -> h (f b)
    K3 c -> c

