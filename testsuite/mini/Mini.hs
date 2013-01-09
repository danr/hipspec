{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),IO,undefined)

data Nat = S Nat | Z deriving (Eq,Show,Typeable,Ord)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in (nats !!) `fmap` choose (0,50)

(+) :: Nat -> Nat -> Nat
Z + y = y
(S x) + y = S (x + y)

plusacc :: Nat -> Nat -> Nat
plusacc Z     y = y
plusacc (S x) y = plusacc x (S y)

prop_1 x y = x + y =:= plusacc x y

prop_2 x y = plusacc x y =:= plusacc y x

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , "Z"       `fun0` Z
    , "S"       `fun1` S
    , "+"       `fun2`  (+)
    , "plusacc" `fun2`  (+)
    ]
