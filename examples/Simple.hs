module Simple where

{-
data J = J1 J | J2 J

j :: J -> J
j x = case x of
    J1 y -> j y
    J2 z -> j z

j2 :: J -> J
j2 x =
    let {-# NOINLINE arg #-}
        arg = case x of
            J1 y -> y
            J2 z -> z
    in  j2 arg

j3 x = j2 x

j4 :: J -> J
j4 x =
    let {-# NOINLINE caser #-}
        caser = j4 x
    in  case caser of
            J1 y -> j4 y
            J2 z -> j4 z

j5 x = const (const (j2 x) (j3 x)) (j4 x)
-}

data K = K1 K | K2 K | K3 K

g,h :: K -> K
g x = K1 x
h x = K2 x

z :: K -> K -> K
z u v = u

f :: K -> K
f x = case z x x of
    K1 a -> g (f a)
    K2 b -> h (f b)
    K3 c -> c
