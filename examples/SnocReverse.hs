module SnocReverse where

import Prelude hiding ((++))
import HipSpec
import List ((++))

snoc :: a -> [a] -> [a]
snoc x []     = [x]
snoc x (y:ys) = y:snoc x ys

rev :: [a] -> [a]
rev (x:xs) = snoc x (rev xs)
rev []     = []

prop_equal xs = rev (rev xs) =:= xs

