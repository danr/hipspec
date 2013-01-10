module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part33_34.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    -- Functions
    , "==" `fun2` (==)
    , "<=" `fun2` (<=)
    , "min" `fun2` (min)
    ]

to_show = (prop_33,prop_34)