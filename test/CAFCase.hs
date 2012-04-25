
-- What happens if you case on a CAF?

module CAFCase where

import Prelude (Bool(..))

-- Good old nats
data Nat = Succ Nat | Zero

-- {-# NOINLINE two #-}
two = Succ (Succ Zero)

foo = case two of
        Zero -> True
        _    -> False