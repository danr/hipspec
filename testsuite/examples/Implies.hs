{-# LANGUAGE TemplateHaskell #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO)

data Nat = S Nat | Z

(+) :: Nat -> Nat -> Nat
Z +   y = y
S x + y = S (x + y)

test_plus :: Nat -> Nat -> Nat -> Prop Nat
test_plus x y z = x + y =:= x + z ==> y =:= z

test :: Bool -> Prop Bool
test x = givenBool x (proveBool x)

tests :: Bool -> Bool -> Prop Bool
tests x y = x =:= y ==> y =:= x

True && a = a
False && a = False

test_and :: Bool -> Bool -> Prop Bool
test_and x y = x && y =:= True ==> y && x =:= True

main :: IO ()
main = hipSpec $(fileName) ([] :: [Sig])

