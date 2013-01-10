module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part22_23.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    -- Functions
    , "max" `fun2` (max)
    ]

to_show = (prop_22,prop_23)