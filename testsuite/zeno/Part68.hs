module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part68.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    , "[]" `fun0` ([] :: [Nat])
    , ":"  `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    -- Functions
    , "==" `fun2` (==)
    , "<=" `fun2` (<=)
    , "len" `fun1` ((len) :: [Nat] -> Nat)
    , "delete" `fun2` ((delete) :: Nat -> [Nat] -> [Nat])
    ]

to_show = (prop_68)