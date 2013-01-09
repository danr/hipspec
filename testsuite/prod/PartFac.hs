{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(undefined,Bool(..), IO, product, Integer, (^), (+), (*), (-), return, Eq, Ord)
import Definitions hiding (Nat, (+), (*))
import Properties
import Data.Typeable

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

nat_fac  = un (\n -> product [1..n])

nat_qfac (Nat 0) acc       = acc
nat_qfac (Nat x) (Nat acc) = nat_qfac (Nat (x - 1)) (Nat (x * acc))

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z", "u"] (undefined :: Nat)
    -- Constructors
    , "Z"      `fun0` nat_z
    , "S"      `fun1` nat_s
    -- Functions
    , "fac"    `fun1` nat_fac
    , "qfac"   `fun2` nat_qfac
    , "+"      `fun2` nat_plus
    , "*"      `fun2` nat_mul
    , withTests 100
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_T33


