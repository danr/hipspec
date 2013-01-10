module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part44.hs"
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: [A])
    -- Constructors
    , "[]" `fun0` ([] :: [A])
    , ":"  `fun2` ((:) :: A -> [A] -> [A])
    -- Functions
    , "zipConcat" `fun3` ((zipConcat) :: A -> [A] -> [A] -> [(A, A)])
    , "zip" `fun2` ((zip) :: [A] -> [A] -> [(A,A)])
    ]

to_show = (prop_44)