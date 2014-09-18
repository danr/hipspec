module SnocReverse where

import Prelude hiding ((++))
import HipSpec
import List ((++))

rev :: [a] -> [a]
rev (x:xs) = snoc x (rev xs)
rev []     = []

prop_bogus xs = rev (rev xs) =:= xs

snoc :: a -> [a] -> [a]
snoc x []     = [id x]
snoc x (y:ys) = y:snoc x ys









{-
qrev :: [a] -> [a] -> [a]
qrev []     ys = ys
qrev (x:xs) ys = qrev xs (x:ys)

prop_equal xs = qrev xs [] =:= rev xs

{-
prop_rev xs ys = rev xs ++ rev ys =:= rev (ys ++ xs)

prop_inv xs = rev (rev xs) =:= xs

prop_assoc xs ys zs = (xs ++ ys) ++ zs =:= xs ++ (ys ++ zs)

prop_rid xs = xs ++ [] =:= xs
-}
-}
