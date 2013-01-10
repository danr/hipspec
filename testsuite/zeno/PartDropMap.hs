{-# LANGUAGE TemplateHaskell #-}
module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    , vars ["f", "g"] (undefined :: Nat -> Nat)
    -- Constructors
    , "[]"     `fun0` ([]  :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "map"    `fun2`  (map :: (Nat -> Nat) -> [Nat] -> [Nat])
    , "drop"   `fun2`  (drop :: Nat -> [Nat] -> [Nat])
    -- Observers
    , observer2 (flip ($) :: Nat -> (Nat -> Nat) -> Nat)
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_12

