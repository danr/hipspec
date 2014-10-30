module Integer where

import HipSpec

plus,minus :: Integer -> Integer -> Integer
plus  x y = x + y
minus x y = x - y

plus_comm x y = plus x y =:= plus y x
minus_zero x = isZero (minus x x) =:= True

isZero :: Integer -> Bool
isZero 0 = True
isZero _ = False

eq,ne,lt,le,gt,ge :: Integer -> Integer -> Bool
eq = (==)
ne = (/=)
lt = (<)
le = (<=)
gt = (>)
ge = (>=)

eq_refl   x = eq x x =:= True

ne_irrefl x = ne x x =:= False

lt_irrefl x = lt x x =:= False

le_refl   x = le x x =:= True

gt_irrefl x = gt x x =:= False

ge_refl   x = ge x x =:= True

