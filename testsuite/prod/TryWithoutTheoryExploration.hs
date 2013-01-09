{-# LANGUAGE TemplateHaskell #-}
{-

   Compile with

   ghc --make TryWithoutTheoryExploration.hs -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO)
import Properties
import LemmasAndGeneralizations

-- The properties can be tested without theory exploration mode
main :: IO ()
main = hipSpec $(fileName) ([] :: [Sig])

-- The properties needs to be mentioned here to be included
to_show = (properties, lemmas, generalizations)

