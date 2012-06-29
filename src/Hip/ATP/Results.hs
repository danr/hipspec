{-# LANGUAGE RecordWildCards #-}
module Hip.ATP.Results where

import Data.List
import Data.Maybe
import Data.Function

-- Result from a prover invocation --------------------------------------------

data ProverResult
    = Success
         { successTime :: Integer
         -- ^ Time in milliseconds
         , successLemmas :: Maybe [String]
         -- ^ Just lemmas used if prover is capable of producing a proof
         }
    | Failure
    -- ^ Failure: Timeout/Satisfiable
    | Unknown String
    -- ^ Unrecognised output. For debugging

-- | Make a Success result, but register nothing about lemmas
mkSuccess :: Integer -> ProverResult
mkSuccess time = Success time Nothing

success :: ProverResult -> Bool
success Success{} = True
success _         = False

unknown :: ProverResult -> Bool
unknown Unknown{} = True
unknown _         = False

avgList :: Integral a => [a] -> a
avgList xs = sum xs `div` genericLength xs

flattenProverResults :: [ProverResult] -> ProverResult
flattenProverResults xs
    | all success xs = Success
                           { successTime   = avgList (map successTime xs)
                           , successLemmas = fmap (nub . concat) . sequence
                                           $ map successLemmas xs
                             -- ^ If any of the results were run without
                             --   knowing of lemmas, don't report anything about
                             --   lemmas. Otherwise: nub all used lemmas.
                           }
    | otherwise      = fromMaybe Failure (listToMaybe (filter unknown xs))

instance Eq ProverResult where
  (==) = (==) `on` success

instance Show ProverResult where
  show (Success{..}) = "Success (" ++ show (successTime `div` 1000) ++ " ms)"
  show Failure       = "Failure"
  show (Unknown s)   = "Unknown: " ++ show s

-- Status (result) for an entire property or a proof part ------------------------------

-- Remove this data type in favour of only ProverResult?

data Status
    = None
    | Theorem { statusLemmas :: Maybe [String] }
  deriving (Eq,Ord,Show)

statusFromResults :: [ProverResult] -> Status
statusFromResults [] = None
statusFromResults xs = case flattenProverResults xs of
    Success time lemmas -> Theorem lemmas
    _                   -> None
