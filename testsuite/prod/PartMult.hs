{-# LANGUAGE TemplateHaskell, GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
{-

   Compile with -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO, undefined, Eq, Ord)
import Properties
import Definitions

import Data.Typeable (Typeable)

newtype WrapNat = Wrap Nat deriving (Arbitrary, Typeable, Eq, Ord)

-- It's too slow to make too large terms with mult, so we wrap them in some constructors
mult' :: Nat -> Nat -> Nat -> WrapNat
mult' x y z = Wrap (mult x y z)

unwrap (Wrap x) = x
wrap = Wrap

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["u"]           (undefined :: WrapNat)
    -- Constructors
--    , "Z"      `fun0` Z
--    , "S"      `fun1` S
    -- Functions
    , "wrap"      `fun1` wrap
    , "unwrap"    `fun1` unwrap
    , "mult'"     `fun3` mult'
    , "+"         `fun2` (+)
    , "*"         `fun2` (*)
    ]

-- The properties needs to be mentioned here to be included
to_show = properties

