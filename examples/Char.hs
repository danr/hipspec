module Char where

import HipSpec

prop_char_literal = "lit" =:= 'l':'i':'t':[]

isA :: Char -> Bool
isA 'a' = True
isA _ = False

prop_a = isA 'a' =:= True
prop_b = isA 'b' =:= False

{-
isLit :: String -> Bool
isLit "lit" = True
isLit _ = False
-}

eq,ne,lt,le,gt,ge :: Char -> Char -> Bool
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

