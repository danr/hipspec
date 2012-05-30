{-# LANGUAGE RecordWildCards #-}
module Hip.ResultDatatypes where

import Hip.Trans.ProofDatatypes
import Hip.Util
import Data.Maybe
import Data.Function

-- Result from a prover invocation --------------------------------------------

data ProverResult = Success { successTime :: Integer }
                  -- ^ Success: Theorem or Countersatisfiable
                  | Failure
                  -- ^ Fialure: Satisfiable etc, and timeouts or skipped
                  | Unknown String
                  -- ^ Unreckognized output. For debugging

success :: ProverResult -> Bool
success Success{} = True
success _         = False

unknown :: ProverResult -> Bool
unknown Unknown{} = True
unknown _         = False

flattenProverResults :: [ProverResult] -> ProverResult
flattenProverResults xs
    | all success xs = Success (avgList (map successTime xs))
    | otherwise      = fromMaybe Failure (listToMaybe (filter unknown xs))

instance Eq ProverResult where
  (==) = (==) `on` success

instance Show ProverResult where
  show (Success{..}) = "Success (" ++ show (successTime `div` 1000) ++ " ms)"
  show Failure     = "Failure"
  show (Unknown s) = "Unknown: " ++ show s

-- Status (result) for an entire property or a proof part ------------------------------

data Status = None | FiniteTheorem | Theorem
  deriving (Eq,Ord,Show,Enum,Bounded)

latexStatus :: Status -> String
latexStatus Theorem       = "$\\checkmark_{\\infty}$"
latexStatus FiniteTheorem = "$\\checkmark_{\\mathrm{fin}}$"
latexStatus None          = ""

statuses :: [Status]
statuses = [minBound..maxBound]

statusFromResults :: Coverage -> [ProverResult] -> Status
statusFromResults coverage [] = None
statusFromResults coverage res
    | all success res = case coverage of
                           Infinite -> Theorem
                           Finite   -> FiniteTheorem
    | otherwise = None

