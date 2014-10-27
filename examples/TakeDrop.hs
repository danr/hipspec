module TakeDrop where

import Prelude hiding ((-),(+),(*),take,drop)
import HipSpec
import Nat
import Reverse (rev)

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take :: Nat -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

