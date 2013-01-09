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
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    , vars ["a", "b", "c"] (undefined :: Bool)
    -- Constructors
    , "[]"     `fun0` ([] :: [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    , "True"   `fun0` True
    , "False"  `fun0` False
    -- Functions
    , "drop"   `fun2`  (drop :: Nat -> [Nat] -> [Nat])
    , "elem"   `fun2`  (elem :: Nat -> [Nat] -> Bool)
    , "=="     `fun2`  (==)    -- elem calls (==)
    , "||"     `fun2`  (||)    -- elem calls (||)
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_T39


