{-# LANGUAGE TemplateHaskell, CPP #-}
{-

   Compile with

   ghc --make TryWithoutTheoryExploration.hs -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

-}
module Main where

import Hip.Prelude
import Hip.HipSpec
import Prelude(Bool(..), IO)
import Properties

-- The properties can be tested without theory exploration mode
main :: IO ()
main = hipSpec $(fileName) ([] :: [Sig])

-- The properties needs to be mentioned here to be included
properties = (
#include "Properties.tuple"
    ,
#include "Lemmas.tuple"
    ,
#include "Generalizations.tuple"
    )
