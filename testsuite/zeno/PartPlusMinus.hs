{-# LANGUAGE TemplateHaskell #-}
module Main where

import Prelude(undefined,Bool(..), IO)

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "-"      `fun2` (-)
    , "+"      `fun2` (+)
    ]

-- The properties needs to be mentioned here to be included
to_show = (prop_06, prop_07, prop_08, prop_09)

