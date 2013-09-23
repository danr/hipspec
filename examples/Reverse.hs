module Reverse where

import Prelude hiding (rev,(++))
import HipSpec
import List ((++))

rev (x:xs) = rev xs ++ [x]
rev []     = []

qrev []     ys = ys
qrev (x:xs) ys = qrev xs (x:ys)

prop_equal xs = qrev xs [] =:= rev xs

