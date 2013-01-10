module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part47.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["r", "s", "t"] (undefined :: Tree Nat)
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    , "Leaf" `fun0` (Leaf :: Tree Nat)
    , "Node" `fun3` (Node :: Tree Nat -> Nat -> Tree Nat -> Tree Nat)
    -- Functions
    , "max" `fun2` (max)
    , "height" `fun1` ((height) :: Tree Nat -> Nat)
    , "mirror" `fun1` ((mirror) :: Tree Nat -> Tree Nat)
    ]

to_show = (prop_47)