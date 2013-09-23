{-# LANGUAGE DeriveGeneric,RecordWildCards,NamedFieldPuns,CPP #-}
module HipSpec.Messages where

#ifdef SUPPORT_JSON
import Data.Aeson
#endif
import GHC.Generics
import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Data.Time.Clock
import Numeric
import Text.Printf
import Data.List
import HipSpec.ThmLib
import HipSpec.Params

import HipSpec.Utils
import HipSpec.Utils.Colour

{-# ANN module "HLint: ignore Use camelCase" #-}

data Msg
    = Started

    | Discarded      [String]
    | Candidates     [String]
    | InductiveProof
        { property_name :: String
        , property_repr :: Maybe String
        , used_lemmas   :: Maybe [String]
        , used_provers  :: [String]
        , vars          :: [String]
        }
    | FailedProof
        { property_name :: String
        , property_repr :: Maybe String
        }
    | Loop

    | Spawning            { property_name :: String, prop_ob_info :: ObInfo }
    | SpawningWithTheory  { property_name :: String, prop_ob_info :: ObInfo, theory_string :: String }
    | Cancelling          { property_name :: String, prop_ob_info :: ObInfo }
    | ProverResult        { property_name :: String, prop_ob_info :: ObInfo, std_out :: String }
    | UnknownResult
        { property_name :: String
        , prop_ob_info :: ObInfo
        , used_prover :: String
        , m_stdout :: String
        , m_stderr :: String
        , m_excode :: String
        }

    | FileProcessed
    | DefinitionalEquations [String]
    | QuickSpecDone  { classes :: Int, equations :: Int }
    | StartingUserLemmas
    | Generated String String

    | ExploredTheory [String]
    | Finished
        { proved      :: [(String,Maybe String)]
        , unproved    :: [(String,Maybe String)]
        , qs_proved   :: [(String,Maybe String)]
        , qs_unproved :: [(String,Maybe String)]
        }
  deriving (Eq,Ord,Show,Generic)

csv :: [String] -> String
csv = intercalate ","

showObInfo :: ObInfo -> String
showObInfo (ObInduction{..}) =
    "coords: " ++ csv (map show ind_coords) ++ " " ++
    show ind_num ++ "/" ++ show ind_nums

showMsg :: Params -> Msg -> String
showMsg Params{no_colour,reverse_video} msg = case msg of
    Started        -> "HipSpec started."
    Discarded eqs
        | length eqs > 4 -> "Discarded " ++ show (length eqs) ++
                            " renamings and subsumptions."
        | otherwise      -> "Discarded: " ++ csv eqs
    Candidates eqs -> "Interesting candidates: " ++ csv eqs

    InductiveProof{..} -> green ((not (null vars) ? bold)
        ("Proved " ++ property_name ++ pmif property_repr ++ (case vars of
                [] -> " without induction"
                _  -> " by induction on " ++ csv vars)))
            ++ view_provers used_provers
            ++ view_lemmas used_lemmas

    FailedProof{..} -> "Failed to prove " ++ property_name ++ pmif property_repr

    Spawning{..}           -> "Spawning "   ++ property_name ++ " " ++ showObInfo prop_ob_info
    SpawningWithTheory{..} -> "Spawning "   ++ property_name ++ " " ++ showObInfo prop_ob_info ++ " on:\n" ++ reindent theory_string
    Cancelling{..}         -> "Cancelling " ++ property_name ++ " " ++ showObInfo prop_ob_info
    ProverResult{..}       -> "Finished "   ++ property_name ++ " " ++ showObInfo prop_ob_info ++ ":\n" ++ reindent std_out
    UnknownResult{..}      ->
        "Unknown result from " ++ used_prover ++ " on " ++
        property_name ++ " " ++ showObInfo prop_ob_info ++
        ", exit code: " ++ m_excode ++
        non_null m_stdout ("\n    stdout:\n" ++ reindent (reindent m_stdout)) ++
        non_null m_stderr ("\n    stderr:\n" ++ reindent (reindent m_stderr))

    Loop                   -> "Loop!"

    FileProcessed             -> "File processed."
    DefinitionalEquations eqs -> "Definitional equations:\n" ++ numberedEqs eqs
    QuickSpecDone classes eqs -> "QuickSpec done, " ++ show classes ++ " classes, " ++ show eqs ++ " equations."
    StartingUserLemmas        -> "Starting to prove user lemmas."
    Generated c t             -> "Generated theory for " ++ c ++ ":\n" ++ reindent t

    ExploredTheory eqs -> "Explored theory (proven correct):\n" ++ numberedEqs eqs
    Finished{..} ->
        "Proved:\n" ++ indent (map repr_prop (qs_proved ++ proved)) ++
        if null unproved' then "" else "Unproved:\n" ++ indent unproved'
      where unproved' = map repr_prop (qs_unproved ++ unproved)

  where
    repr_prop :: (String,Maybe String) -> String
    repr_prop (s,ms) = s ++ pmif ms

    pmif :: Maybe String -> String
    pmif Nothing  = ""
    pmif (Just s) = " {- " ++ s ++ " -}"

    non_null :: String -> String -> String
    non_null s m | null s    = ""
                 | otherwise = m

    green = not no_colour ? colour (if reverse_video then Green else Blue)

    numberedEqs :: [String] -> String
    numberedEqs  = unlines . zipWith (printf "%4d: %s") [(1 :: Int)..]

    indent :: [String] -> String
    indent = concatMap (("    "++) . (++"\n"))

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
    UnknownResult{}          -> 10 -- a warning, really
    InductiveProof{vars=_:_} -> 20
    InductiveProof{vars=[]}  -> 30
    FailedProof{}            -> 40
    Loop                     -> 45
    Candidates{}             -> 50
    -- 50: info but quiet
    FileProcessed            -> 60
    Started                  -> 60
    StartingUserLemmas       -> 60
    DefinitionalEquations{}  -> 105
    QuickSpecDone{}          -> 70
    Discarded{}              -> 90
    -- 100: default
    Generated{}              -> 110
    ProverResult{}           -> 120
    Spawning{}               -> 130
    Cancelling{}             -> 140
    SpawningWithTheory{}     -> 200

#ifdef SUPPORT_JSON
instance ToJSON Msg
#endif

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

