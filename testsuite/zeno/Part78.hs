module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part78.hs"
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: [A])
    -- Constructors
    , "[]" `fun0` ([] :: [A])
    , ":"  `fun2` ((:) :: A -> [A] -> [A])
    -- Functions
    , "sort" `fun1` ((sort) :: [Nat] -> [Nat])
    , "sorted" `fun1` ((sorted) :: [Nat] -> Bool)
    ]

to_show = (prop_78)