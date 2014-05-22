module Reverse where

import Prelude hiding ((++))
import HipSpec
import List ((++))

rev :: [a] -> [a]
rev (x:xs) = rev xs ++ [x]
rev []     = []

prop_bogus xs = rev xs =:= xs








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
