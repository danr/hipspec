module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part31_32.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    -- Functions
    , "min" `fun2` (min)
    ]

to_show = (prop_31,prop_32)