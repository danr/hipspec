{-# LANGUAGE TemplateHaskell #-}
{-

   Compile with -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO, undefined)
import Properties
import Definitions


main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    -- Constructors
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "half"   `fun1`  half
    , "+"      `fun2`  (+)
    ]

-- The properties needs to be mentioned here to be included
to_show = (prop_T26, prop_T13)

