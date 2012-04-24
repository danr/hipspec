module Eq where

import Prelude (Eq(..),Bool(..))

data K = X | Y | Z deriving Eq

equals :: K -> K -> Bool
equals = (==)