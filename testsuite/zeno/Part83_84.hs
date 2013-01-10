module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part83_84.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    , "[]" `fun0` ([] :: [Nat])
    , ":"  `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    -- Functions
    , "++" `fun2` ((++) :: [Nat] -> [Nat] -> [Nat])
    , "drop" `fun2` ((drop) :: Nat -> [Nat] -> [Nat])
    , "len" `fun1` ((len) :: [Nat] -> Nat)
    , "zip" `fun2` ((zip) :: [Nat] -> [Nat] -> [(Nat,Nat)])
    , "take" `fun2` ((take) :: Nat -> [Nat] -> [Nat])
    ]

to_show = (prop_83,prop_84)