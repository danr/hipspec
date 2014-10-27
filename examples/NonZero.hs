module NonZero where

import Prelude hiding ((-),(+),(*),(<),gcd)
import HipSpec
import Nat

nz Z = Z
nz (S n) = nz (nz n)

ri Z     = Z
ri (S n) = S (ri (ri n))
