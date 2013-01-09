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
    x <- choose (0,3)
    return (Nat x)

un  op  (Nat x)         = Nat (op x)
bin (#) (Nat x) (Nat y) = Nat (x # y)

nat_z    = Nat 0
nat_s    = un (+1)
nat_plus = bin (+)
nat_mul  = bin (*)

nat_exp = bin (^)

nat_qexp _       (Nat 0) acc       = acc
nat_qexp (Nat x) (Nat n) (Nat acc) = nat_qexp (Nat x) (Nat (n - 1)) (Nat (x * acc))

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
--    , "Z"      `fun0` nat_z
--    , "S"      `fun1` nat_s
    -- Functions
    , "+"      `fun2` nat_plus
    , "*"      `fun2` nat_mul
    , "exp"    `fun2` nat_exp
    , "qexp"   `fun3` nat_qexp
    ]

-- The properties needs to be mentioned here to be included
to_show = properties


