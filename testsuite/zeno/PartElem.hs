{-# LANGUAGE TemplateHaskell #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(undefined,Bool(..), IO)
import Definitions
import Properties

-- The properties can be tested without theory exploration mode
main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "[]"     `fun0` ([]  :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "++"     `fun2` ((++)   :: [Nat] -> [Nat] -> [Nat])
    , "elem"   `fun2` elem
    , "=="     `fun2` (==)
    ]

-- The properties needs to be mentioned here to be included
to_show = properties

