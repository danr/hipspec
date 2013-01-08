{-# LANGUAGE TemplateHaskell #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(undefined,Bool(..), IO)
import Definitions
import Properties

-- The properties can be tested without theory exploration mode
main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "max"    `fun2` max
    ]

-- The properties needs to be mentioned here to be included
to_show = properties


