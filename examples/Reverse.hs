module Reverse where

import Prelude hiding ((++))
import HipSpec
import List ((++))

rev :: [a] -> [a]
rev (x:xs) = rev xs ++ [x]
rev []     = []

qrev :: [a] -> [a] -> [a]
qrev []     ys = ys
qrev (x:xs) ys = qrev xs (x:ys)

prop_equal xs = qrev xs [] =:= rev xs

