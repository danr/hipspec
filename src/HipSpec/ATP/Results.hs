{-# LANGUAGE RecordWildCards #-}
module HipSpec.ATP.Results where

import Data.List
import Data.Maybe
import Data.Function

-- Result from a prover invocation --------------------------------------------

data ProverResult
    = Success
         { successLemmas :: Maybe [String]
         -- ^ Just lemmas used if prover is capable of producing a proof
         }
    | Failure
    -- ^ Failure: Timeout/Satisfiable
    | Unknown String
    -- ^ Unrecognised output. For debugging

-- | Make a Success result, but register nothing about lemmas
mkSuccess :: ProverResult
mkSuccess = Success Nothing

success :: ProverResult -> Bool
success Success{} = True
success _         = False

failure :: ProverResult -> Bool
failure = not . success

unknown :: ProverResult -> Bool
unknown Unknown{} = True
unknown _         = False

instance Eq ProverResult where
  (==) = (==) `on` success

instance Show ProverResult where
  show (Success{..}) = "Success"
  show Failure       = "Failure"
  show (Unknown s)   = "Unknown: " ++ show s

