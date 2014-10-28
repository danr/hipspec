{-
   Command Line Parameter Options

   Uses Neil Mitchell's cmdargs

   In this file it is OK to have lines with >80 characters
-}
{-# LANGUAGE DeriveDataTypeable,CPP #-}
module HipSpec.Params
    ( Params(..)
    , defParams
    , sanitizeParams
    , cmdArgs
    , DebugFlag(..)
    , Technique(..)
    , SuccessOpt(..)
    , whenFlag
    ) where

import System.Console.CmdArgs hiding (verbosity,auto)
import HipSpec.ATP.Provers
import Data.Maybe(isNothing)
import Data.Char
import Data.List (intercalate)
import Data.List.Split
import Control.Monad(when)

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Debugging flags
data DebugFlag
    = PrintParams
    | PrintCore
    | PrintRich
    | PrintOptRich
    | PrintSimple
--    | PrintFunFO
    | PrintPolyFOL
    | LintPolyFOL
    | DebugStrConv
    | DebugMono
    | TranslateOnly
    | PrintProps

    | PrintAutoSig
    | DebugAutoSig

--    | PrintCallGraph
--    | PrintDefinitions
--    | PrintEqClasses
    | QuickSpecOnly
    | QuickSpecDebug
  deriving (Eq,Ord,Show,Enum,Bounded,Data,Typeable)

defStr :: Eq a => a -> [a] -> String
defStr x xs | x `elem` xs = " (default)"
            | otherwise   = ""

-- | Descriptions of debug flags
debugDesc :: DebugFlag -> String
debugDesc flg = case flg of
    PrintParams      -> "Print the passed parameters"
    PrintCore        -> "Print GHC Core"
    PrintRich        -> "Print Rich IR"
    PrintOptRich     -> "Print Optimised Rich IR"
    PrintSimple      -> "Print Simple IR"
--    PrintFunFO       -> "Print First-Order Functional IR"
    PrintPolyFOL     -> "Print Polymorphic FOL"
    LintPolyFOL      -> "Use alt-ergo to lint Polymorphic FOL"
    DebugStrConv     -> "Print string conversions in signature"
    DebugMono        -> "Print monomorphisation debugging"
    TranslateOnly    -> "Stop after translating"
    PrintProps       -> "Print properties"

    PrintAutoSig     -> "Print generated signature"
    DebugAutoSig     -> "Print information about generated signature"

--    PrintCallGraph   -> "Print the call graph"
--    PrintDefinitions -> "Print definitions translated to QuickSpec eqns"
--    PrintEqClasses   -> "Print initial equivalence classes from QuickSpec"
    QuickSpecOnly    -> "Stop after QuickSpec"
    QuickSpecDebug   -> "Debug what QuickSpec is doing"

-- | Makes a nice flag from a constructor string
--   e.g. PrintPolyFOL becomes print-poly-fol
flagifyString :: String -> String
flagifyString
    = map toLower . intercalate "-"
    . split (condense $ dropInitBlank $ keepDelimsL $ whenElt isUpper)

flagify :: Show a => a -> String
flagify = flagifyString . show

data Technique = Induction | Plain | FixpointInduction
  deriving (Eq,Ord,Show,Enum,Bounded,Data,Typeable)

defaultTechs :: [Technique]
defaultTechs = [Induction,Plain]

data SuccessOpt = CleanRun | NothingUnproved | ProvesUserStated
  deriving (Eq,Ord,Show,Enum,Bounded,Data,Typeable)

-- | Parameters
data Params = Params
    { file                :: FilePath
    , verbosity           :: Int
    , output              :: Maybe FilePath
    , reverse_video       :: Bool
    , no_colour           :: Bool
    , z_encode_filenames  :: Bool
    , tr_mod              :: Bool
    , directory           :: Maybe FilePath
#ifdef SUPPORT_JSON
    , json                :: Maybe FilePath
#endif
{-
    , isabelle_mode       :: Bool
    , cond_name           :: String
    , cond_count          :: Int
-}

    , processes           :: Int
    , timeout             :: Double
    , expand_boolprops    :: Bool

    , isolate             :: Bool
    , only_user_stated    :: Bool
    , only                :: [String]
    , add_stupid_lemmas   :: Bool
    , success             :: SuccessOpt
    , techniques          :: [Technique]
    , provers             :: [ProverName]

{-
    , user_stated_first   :: Bool
    , explore_theory      :: Bool
    , call_graph          :: Bool
-}

    , auto                :: Bool
    , extra               :: [String]
    , extra_trans         :: [String]
    , qspruner            :: Bool
    , termsize            :: Int

    {-
    , pvars               :: Bool
    -}


    , inddepth            :: Int
    , indvars             :: Int
    , indhyps             :: Int
    , indobligs           :: Int

    , debug_flags         :: [DebugFlag]
    }
  deriving (Show,Data,Typeable)

-- | Sanitize the paramaters:
--
-- If you are using a theorem prover that cannot stdin then put on output.
--
-- If no theorem prover is specified, use the default theorem provers
--
-- Previously: We cannot have --smt-data-types when using --bottoms.
sanitizeParams :: Params -> Params
sanitizeParams
    = {- fix_isabelle_mode
    . -} fix_stdin
    . fix_empty_provers
    . fix_empty_techniques
 {- . fix_smt_data_types -}
  where
{-
    fix_isabelle_mode params
        | isabelle_mode params = params
            { debug_flags    = debug_flags params
            , explore_theory = True
            , verbosity      = 0
            , auto           = True
            }
        | otherwise = params
-}

    fix_stdin params
        | any prover_cannot_stdin provers' = params
            { output = if isNothing (output params)
                           then Just "proving"
                           else output params
            }
        | otherwise = params
      where
        provers' = proversFromNames (provers params)

    fix_empty_provers params
        | null (provers params) = params { provers = defaultProverNames }
        | otherwise             = params

    fix_empty_techniques params
        | null (techniques params) = params { techniques = defaultTechs }
        | otherwise                = params

{-
    fix_smt_data_types params
        | bottoms params && smt_data_types params = params
            { smt_data_types = False }
        | otherwise = params
-}


-- | Default parameters
defParams :: Params
defParams = Params
    { file                = ""      &= argPos 0  &= typFile
    , output              = Nothing &= name "o"  &= opt "proving" &= typDir &= help "Save files from obligations in a directory"
    , verbosity           = 100                  &= help "Verbosity (default 100)"
    , no_colour           = False                &= help "Do not print in colour"
    , reverse_video       = False   &= name "rv" &= help "Reverse video (assume black terminal background)"
    , z_encode_filenames  = False   &= name "z"  &= help "Z-encode filenames (necessary for windows)"
    , directory           = Nothing &= name "dir" &= help "Change into directory before trying to load file"
#ifdef SUPPORT_JSON
    , json                = Nothing &= typFile   &= help "File to write statistics to (in json format)"
#endif
--     , isabelle_mode       = False                &= help "Isabelle mode"
--     , cond_name           = ""                   &= help "Isabelle: pre-condition name"
--     , cond_count          = 1                    &= help "Isabelle: pre-condition count"
    , only                = []                   &= help "Only try these user properties (affects --auto)"
    , tr_mod              = False                &= help "Unconditonally translate all module bindings"
    , add_stupid_lemmas   = False                &= help "Also use theorems proved without induction as lemmas"
    , success             = CleanRun             &= help "Specify what to give exit code 0"

    , auto                = True    &= groupname "\nSignature generation settings"
                                    &= name "a" &= help "Make signature with functions in user properties (def. on)"
    , extra               = []                  &= help "Additional functions to add to the signature"
    , extra_trans         = []                  &= help "Like --extra, but transitively"
    , qspruner            = False               &= help "Use the default QuickSpec pruner"
    , termsize            = 7                   &= help "QuickSpec term size"

    {-
    , pvars               = False               &= help "Use pvars instead of vars in the auto signature"
    , quick_check_size    = 20                  &= help "Set the withQuickCheckSize (default 20)"
    , tests               = 100                 &= help "Set the withTests          (default 100)"
    , size                = 1000                &= help "Set the withSize           (default \"unlimited\")"

-}
    , processes           = 2    &= groupname "\nProving settings"
                                 &= name "N" &= help "Prover processes          (default 2)"
    , timeout             = 1    &= name "t" &= help "Prover timeout in seconds (default 1.0)"
    , expand_boolprops    = False            &= help "Expand boolean properties to implication form"

    , techniques = enumerate
         [ (t,show t ++ defStr t defaultTechs)
         | t <- [minBound..maxBound]
         ]

    , provers = enumerate
        [ (pn,prover_desc p ++ defStr pn defaultProverNames)
        | pn <- allProverNames
        , let p = proverFromName pn
        ]
        &= groupname "\nBackends (may select multiple)"

    , isolate             = False   &= name "l" &= help "Do not use user stated properties as lemmas"
    , only_user_stated    = False   &= name "u" &= help "Stop when all user stated properties are proved"

{-
    , explore_theory      = False               &= help "Print explored theory"

    , user_stated_first   = False   &= name "U" &= help "Put user stated properties first in the loop"

    , prepend_pruned      = False   &= name "r" &= help "Add nice pruned equations in front of queue"
    , call_graph          = True    &= name "c" &= name "cg" &= help "Sort equations by the call graph (def. on)"
-}

    , inddepth            = 1       &= name "d" &= groupname "\nStructural induction"
                                                &= help "Maximum depth       (default 1)"
    , indvars             = 2       &= name "v" &= help "Maximum variables   (default 2)"
    , indhyps             = 200     &= name "H" &= help "Maximum hypotheses  (default 200)"
    , indobligs           = 25      &= name "O" &= help "Maximum obligations (default 25)"

    , debug_flags = enumerate
         [ (f,debugDesc f) | f <- [minBound..maxBound] ]
         &= groupname "\nDebugging"
    }
    &= summary (logo ++ "\n v3.1 by Dan Rosén, danr@chalmers.se")
    &= program "hipspec"

enumerate :: (Show val,Data val) => [(val,String)] -> [val]
enumerate xs = enum $
    [] &= ignore :
    [ [x] &= name (flagify x) &= help h | (x,h) <- xs ]

whenFlag :: Monad m => Params -> DebugFlag -> m () -> m ()
whenFlag p flg = when (flg `elem` debug_flags p)

logo :: String
logo = map (\ x -> if x == 'z' then '\\' else if x == 'w' then '\"' else x) $ unlines
    [ "  _     _                           "
    , " | |   (_)                          "
    , " | |__  _ _ __  ___ _ __   ___  ___ "
    , " | '_ z| | '_ z/ __| '_ z / _ z/ __|"
    , " | | | | | |_) z__ z |_) |  __/ (__ "
    , " |_| |_|_| .__/|___/ .__/ z___|z___|"
    , "         | |       | |              "
    , "         |_|  wUpp |_| till bevis!w "
    ]
