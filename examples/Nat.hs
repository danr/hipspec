{-# LANGUAGE DeriveDataTypeable #-}
module Nat where

import Prelude hiding ((+),(*))
import HipSpec

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * _ = Z

instance Names Nat where
  names _ = ["m","n","o"]
