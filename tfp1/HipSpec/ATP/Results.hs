{-# LANGUAGE RecordWildCards #-}
module HipSpec.ATP.Results where

import Data.Function
import Control.Concurrent.STM.Promise.Process (ProcessResult)

-- Result from a prover invocation --------------------------------------------

data ProverResult
    = Success
         { successLemmas :: Maybe [Int]
         -- ^ Just lemmas used if prover is capable of producing a proof
         }
    | Unknown ProcessResult
    -- ^ Unrecognised output. For debugging

-- | Make a Success result, but register nothing about lemmas
mkSuccess :: ProverResult
mkSuccess = Success Nothing

success :: ProverResult -> Bool
success Success{} = True
success _         = False

unknown :: ProverResult -> Bool
unknown Unknown{} = True
unknown _         = False

instance Eq ProverResult where
  (==) = (==) `on` success

instance Show ProverResult where
  show (Success{..}) = "Success"
  show (Unknown s)   = "Unknown: " ++ show s

