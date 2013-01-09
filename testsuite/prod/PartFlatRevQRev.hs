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


main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"]       (undefined :: A)
    , vars ["xs", "ys", "zs"]    (undefined :: [A])
    , vars ["xss", "yss", "zss"] (undefined :: [[A]])
    -- Constructors
    , "[]"     `fun0` ([] :: [A])
    , ":"      `fun2` ((:) :: A -> [A] -> [A])
    , "[]"     `fun0` ([] :: [[A]])
    , ":"      `fun2` ((:) :: [A] -> [[A]] -> [[A]])
    -- Functions
    , "++"       `fun2`  ((++)     :: [A] -> [A] -> [A])       -- revflat calls (++)
    , "++"       `fun2`  ((++)     :: [[A]] -> [[A]] -> [[A]]) -- revflat calls (++)
    , "revflat"  `fun1`  (revflat  :: [[A]] -> [A])
    , "qrevflat" `fun2`  (qrevflat :: [[A]] -> [A] -> [A])
    ]

-- The properties needs to be mentioned here to be included
to_show = prop_T28

