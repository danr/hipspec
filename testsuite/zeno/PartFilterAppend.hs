{-# LANGUAGE TemplateHaskell #-}
module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: A)
    , vars ["xs", "ys", "zs"] (undefined :: [A])
    , vars ["p", "q"] (undefined :: A -> Bool)
    -- Constructors
    , "[]"     `fun0` ([]  :: [A])
    , ":"      `fun2` ((:) :: A -> [A] -> [A])
    -- Functions
    , "++"     `fun2`  ((++)   :: [A] -> [A] -> [A])
    , "filter" `fun2`  (filter :: (A -> Bool) -> [A] -> [A])
    -- Observers
    , observer2 (flip ($) :: A -> (A -> Bool) -> Bool)
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_14

