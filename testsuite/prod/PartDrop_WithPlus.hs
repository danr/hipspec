module PartDrop_WithPlus (sig, module Definitions) where

import HipSpec.Prelude
import Prelude(Bool(..), IO, undefined)
import Properties
import Definitions

sig = signature
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "[]"     `fun0` ([] :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    , "Z"      `fun0` Z
    , "S"      `fun1` S
    -- Functions
    , "drop"   `fun2`  (drop   :: Nat -> [Nat] -> [Nat])
    , "+"      `fun2`  (+)
    ]

-- The properties needs to be mentioned here to be included
to_show =
    ( prop_T08
    , prop_T09
    )


