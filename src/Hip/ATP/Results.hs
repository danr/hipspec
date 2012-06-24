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
    -- ^ Success: Theorem/Unsatisfiable
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
    | all success xs = Success (avgList (map successTime xs))
    | otherwise      = fromMaybe Failure (listToMaybe (filter unknown xs))

instance Eq ProverResult where
  (==) = (==) `on` success

instance Show ProverResult where
  show (Success{..}) = "Success (" ++ show (successTime `div` 1000) ++ " ms)"
  show Failure       = "Failure"
  show (Unknown s)   = "Unknown: " ++ show s

-- Status (result) for an entire property or a proof part ------------------------------

data Status = None | Theorem
  deriving (Eq,Ord,Show,Enum,Bounded)

statusFromResults :: [ProverResult] -> Status
statusFromResults [] = None
statusFromResults res
    | all success res = Theorem
    | otherwise = None

