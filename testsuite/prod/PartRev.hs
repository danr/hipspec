{-# LANGUAGE TemplateHaskell #-}
{-

   Compile with -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO, undefined)
import Properties
import Definitions
import Tuples

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["a", "b", "c"] (undefined :: Bool)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "[]"     `fun0` ([] :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "++"     `fun2`  ((++)   :: [Nat] -> [Nat] -> [Nat])
    , "qrev"   `fun2`  (qrev   :: [Nat] -> [Nat] -> [Nat])
    , "rev"    `fun1`  (rev    :: [Nat] -> [Nat])
    , "length" `fun1`  (length :: [Nat] -> Nat)
    , "+"      `fun2`  (+)
    ]

-- The properties needs to be mentioned here to be included
to_show = properties

