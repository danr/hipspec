{-# LANGUAGE TemplateHaskell #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(undefined,Bool(..), IO)
import Definitions
import Properties

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "[]"     `fun0` ([]  :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    , "True"   `fun0` True
    -- Functions
    , "rev"    `fun1`  (rev    :: [Nat] -> [Nat])
    , "++"     `fun2`  ((++)   :: [Nat] -> [Nat] -> [Nat])
    , "count"  `fun2`  (count  :: Nat -> [Nat] -> Nat)
    , "=="     `fun2`  (==)
    , "-"      `fun2`  (-)
    ]

-- The properties needs to be mentioned here to be included
to_show = properties

