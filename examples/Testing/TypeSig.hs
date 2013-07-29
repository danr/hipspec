module TypeSig where

import HipSpec

type Boolean = Bool

prop :: Boolean -> Prop Bool
prop x = x =:= x

