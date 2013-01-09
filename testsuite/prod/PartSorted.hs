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
    [ vars ["x", "y", "z"]    (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "[]"     `fun0` ([] :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "<="        `fun2` (<=) -- sorted, insert calls (<=)
    , "&&"        `fun2` (&&) -- sorted calls (&&)
    , "isort"     `fun1` isort
    , "sorted"    `fun1` sorted
    , "insert"    `fun2` insert
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_T14

