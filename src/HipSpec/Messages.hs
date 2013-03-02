{-# LANGUAGE DeriveGeneric,RecordWildCards, ExistentialQuantification #-}
module HipSpec.Messages where

import Data.Aeson
import GHC.Generics
import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Data.Time.Clock
import Numeric
import Text.Printf
import Data.List
import HipSpec.Trans.Obligation

data Msg
    = Started

    -- MainLoop

    | Discarded      [String]
    | Candidates     [String]
    | InductiveProof { prop_name :: String, used_lemmas :: Maybe [String], used_provers :: [String], vars :: [String] }
    | FailedProof    { prop_name :: String }
    | Loop

    -- Invoke

    | Spawning            { prop_name :: String, prop_ob_info :: ObInfo }
    | SpawningWithTheory  { prop_name :: String, prop_ob_info :: ObInfo, theory_string :: String }
    | Cancelling          { prop_name :: String, prop_ob_info :: ObInfo }
    | ProverResult        { prop_name :: String, prop_ob_info :: ObInfo, std_out :: String }

    -- HipSpec

    | FileProcessed
    | DefinitionalEquations [String]
    | QuickSpecDone  { classes :: Int, equations :: Int }
    | StartingUserLemmas

    | ExploredTheory [String]
    | Finished
        { proved :: [String]
        , unproved :: [String]
        , qs_proved :: [String]
        , qs_unproved :: [String]
        }
  deriving (Eq, Ord, Show, Generic)

csv :: [String] -> String
csv = intercalate ","

showObInfo :: ObInfo -> String
showObInfo (Induction{..}) =
    "coords: " ++ csv (map show ind_coords) ++ " " ++
    show ind_num ++ "/" ++ show ind_nums

showMsg :: Msg -> String
showMsg m = case m of
    Started        -> "HipSpec started."
    Discarded eqs
        | length eqs > 4 -> "Discarded " ++ show (length eqs) ++
                            " renamings and subsumptions."
        | otherwise      -> "Discarded: " ++ csv eqs
    Candidates eqs -> "Interesting candidates: " ++ csv eqs

    InductiveProof{..} ->
        "Proved " ++ prop_name ++ (case vars of
                [] -> " without induction"
                _  -> " by induction on " ++ csv vars)
            ++ view_provers used_provers
            ++ view_lemmas used_lemmas

    FailedProof{..} -> "Failed to prove " ++ prop_name

    Spawning{..}           -> "Spawning "   ++ prop_name ++ " " ++ showObInfo prop_ob_info
    SpawningWithTheory{..} -> "Spawning "   ++ prop_name ++ " " ++ showObInfo prop_ob_info ++ "on :\n" ++ reindent theory_string
    Cancelling{..}         -> "Cancelling " ++ prop_name ++ " " ++ showObInfo prop_ob_info
    ProverResult{..}       -> "Finished "   ++ prop_name ++ " " ++ showObInfo prop_ob_info ++ ":\n" ++ reindent std_out

    Loop                   -> "Loop!"

    FileProcessed             -> "File processed."
    DefinitionalEquations eqs -> "Definitional equations:\n" ++ numberedEqs eqs
    QuickSpecDone classes eqs -> "QuickSpec done, " ++ show classes ++ " classes, " ++ show eqs ++ " equations."
    StartingUserLemmas        -> "Starting to prove user lemmas."

    ExploredTheory eqs -> "Explored theory (proven correct):\n" ++ numberedEqs eqs
    Finished{..} ->
        "Proved:\n" ++ indent (qs_proved ++ proved) ++
        "Unproved:\n " ++ indent (qs_unproved ++ unproved)
  where
    numberedEqs :: [String] -> String
    numberedEqs  = unlines . zipWith (printf "%4d: %s") [(1 :: Int)..]

    indent :: [String] -> String
    indent = unlines . map ("    "++)

    reindent :: String -> String
    reindent = indent . lines

    view_provers ps = " using " ++ csv ps

    view_lemmas mx = case mx of
        Nothing  -> ""
        Just []  -> ", using no lemmas"
        Just [x] -> ", using " ++ x
        Just xs  -> ", using: " ++ concatMap ("\n\t" ++) xs ++ "\n"

msgVerbosity :: Msg -> Int
msgVerbosity m = case m of
    ExploredTheory{}         -> 0  -- enabled by a flag
    Finished{}               -> 1  -- most interesting
    InductiveProof{vars=_:_} -> 20
    InductiveProof{vars=[]}  -> 30
    FailedProof{}            -> 40
    Loop                     -> 45
    Candidates{}             -> 50
    -- 50: info but quiet
    FileProcessed            -> 60
    Started                  -> 60
    StartingUserLemmas       -> 60
    DefinitionalEquations{}  -> 80
    QuickSpecDone{}          -> 70
    Discarded{}              -> 90
    -- 100: default
    ProverResult{}           -> 110
    Spawning{}               -> 120
    Cancelling{}             -> 130
    SpawningWithTheory{}     -> 200

instance ToJSON Msg

mkWriter :: IO (Msg -> IO (), IO [(Double,Msg)])
mkWriter = do

    t0 <- getCurrentTime

    msgs <- newTVarIO []

    let obtain = fmap reverse $ atomically $ readTVar msgs

        write m = do
            t1 <- getCurrentTime
            let t :: Double
                t = fromRat (toRational (diffUTCTime t1 t0))
            atomically $ modifyTVar msgs ((t,m):)

    return (write,obtain)

