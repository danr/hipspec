module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part12.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    , vars ["f", "g"] (undefined :: Nat -> Nat)
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    , "[]" `fun0` ([] :: [Nat])
    , ":"  `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    -- Functions
    , "drop" `fun2` ((drop) :: Nat -> [Nat] -> [Nat])
    , "map" `fun2` ((map) :: (Nat -> Nat) -> [Nat] -> [Nat])
    -- Observers
    , observer2 (flip ($) :: Nat -> (Nat -> Nat) -> Nat)
    ]

to_show = (prop_12)