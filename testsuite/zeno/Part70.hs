module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part70.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    -- Functions
    , "<=" `fun2` (<=)
    ]

to_show = (prop_70)