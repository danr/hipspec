module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec "Part43.hs"
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: [A])
    , vars ["p", "q"] (undefined :: A -> Bool)
    -- Constructors
    , "[]" `fun0` ([] :: [A])
    , ":"  `fun2` ((:) :: A -> [A] -> [A])
    -- Functions
    , "takeWhile" `fun2` ((takeWhile) :: (A -> Bool) -> [A] -> [A])
    , "dropWhile" `fun2` ((dropWhile) :: (A -> Bool) -> [A] -> [A])
    , "++" `fun2` ((++) :: [A] -> [A] -> [A])
    -- Observers
    , observer2 (flip ($) :: A -> (A -> Bool) -> Bool)
    ]

to_show = (prop_43)