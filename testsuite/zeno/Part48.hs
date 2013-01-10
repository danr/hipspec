module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part48.hs"
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: [A])
    -- Constructors
    , "[]" `fun0` ([] :: [A])
    , ":"  `fun2` ((:) :: A -> [A] -> [A])
    -- Functions
    , "++" `fun2` ((++) :: [A] -> [A] -> [A])
    , "butlast" `fun1` ((butlast) :: [A] -> [A])
    , "null" `fun1` ((null) :: [A] -> Bool)
    ]

to_show = (prop_48)