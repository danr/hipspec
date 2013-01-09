{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Main where

import Prelude hiding ((+),(*),even,odd,sum,id)
import HipSpec
import HipSpec.Prelude
import Data.Typeable

data Nat = Z | S Nat
  deriving (Eq,Ord,Show,Typeable)

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
_   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
_   * m = Z

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (error "Nat type" :: Nat)
    , fun0 "Z" Z
    , fun1 "S" S
    , fun2 "+" (+)
    , fun2 "*" (*)
    ]

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized arbSized

arbSized s = do
  x <- choose (0,round (sqrt (toEnum s)))
  return (toEnum x)

