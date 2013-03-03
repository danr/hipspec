module HipSpec.Void where

data Void = Void !Void
  deriving (Eq,Ord,Show)

absurd :: Void -> a
absurd (Void void) = absurd void

