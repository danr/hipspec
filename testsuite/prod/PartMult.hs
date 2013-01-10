{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(undefined,Bool(..), IO, product, Integer, (^), (+), (*), (-), return, Eq, Ord)
import Definitions hiding (Nat, (+), (*))
import Properties
import Data.Typeable

newtype Wrap a = Wrap a deriving (Typeable, Eq, Ord, Arbitrary)

newtype Nat = Nat Integer
  deriving (Typeable, Eq, Ord)

instance Arbitrary Nat where
  arbitrary = do
    x <- choose (0,5)
    return (Nat x)

un  op  (Nat x)         = Nat (op x)
bin (#) (Nat x) (Nat y) = Nat (x # y)

nat_z    = Nat 0
nat_s    = un (+1)
nat_plus = bin (+)
nat_mul  = bin (*)

nat_mult :: Nat -> Nat -> Nat -> Wrap Nat
nat_mult (Nat 0) _       acc       = Wrap acc
nat_mult (Nat n) (Nat y) (Nat acc) = nat_mult (Nat (n - 1)) (Nat y) (Nat (y + acc))

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z", "u"] (undefined :: Nat)
    -- Constructors
    , "Z"      `fun0` nat_z
    , "S"      `fun1` nat_s
    -- Functions
    , "+"      `fun2` nat_plus
    , "*"      `fun2` nat_mul
    , "mult"   `fun3` nat_mult
    , withTests 100
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_T34

