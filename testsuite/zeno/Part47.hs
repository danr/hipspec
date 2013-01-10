module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part47.hs"
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["r", "s", "t"] (undefined :: Tree A)
    -- Constructors
    , "Leaf" `fun0` (Leaf :: Tree A)
    , "Node" `fun3` (Node :: Tree A -> A -> Tree A -> Tree A)
    -- Functions
    , "mirror" `fun1` ((mirror) :: Tree A -> Tree A)
    , "height" `fun1` ((height) :: Tree A -> Nat)
    ]

to_show = (prop_47)