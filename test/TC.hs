module TC where

import Prelude ()

data Bool = True | False

class IsZero a where
  isZero :: a -> Bool

instance IsZero Bool where isZero x = x

data Nat = Succ Nat | Zero

instance IsZero Nat where
  isZero Zero = True
  isZero _    = False

data Unit = Unit

instance IsZero Unit where isZero _ = True
