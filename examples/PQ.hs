module PQ where

import Prelude hiding ((+),(<))
import HipSpec
import Nat

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

p Z = True
p (S x) = p x && q x (S x)

q x Z = True
q x (S y) = p x && q x y

prop_p x = p x =:= True

prop_q x y = q x y =:= True

-- prop_p_str x = y - x =:= n ==> p x =:= True

prop_pqr x y z = p x && q y z =:= True

prop_pqr2 x y z = p x =:= q y z
