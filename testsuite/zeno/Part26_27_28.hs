module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part26_27_28.hs"
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "Z" `fun0` Z
    , "S" `fun1` S
    , "[]" `fun0` ([] :: [Nat])
    , ":"  `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    -- Functions
    , "elem" `fun2` ((elem) :: Nat -> [Nat] -> Bool)
    , "++" `fun2` ((++) :: [Nat] -> [Nat] -> [Nat])
    ]

to_show = (prop_26,prop_27,prop_28)