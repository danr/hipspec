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
--    | PrintRich
    | PrintSimple
--    | PrintFunFO
    | PrintPolyFOL
    | LintPolyFOL
    | PrintProps
    | PrintDefinitions
    | PrintCallGraph
    | PrintAutoSig
    | DebugAutoSig
    | DebugStrConv
    | PrintEqClasses
    | TranslateOnly
    | QuickSpecOnly
  deriving (Eq,Ord,Show,Enum,Bounded,Data,Typeable)

defStr :: Eq a => a -> [a] -> String
defStr x xs | x `elem` xs = " (default)"
            | otherwise   = ""

-- | Descriptions of debug flags
debugDesc :: DebugFlag -> String
debugDesc flg = case flg of
    PrintParams      -> "Print the passed parameters"
    PrintCore        -> "Print GHC Core"
--    PrintRich        -> "Print Rich IR"
    PrintSimple      -> "Print Simple IR"
--    PrintFunFO       -> "Print First-Order Functional IR"
    PrintPolyFOL     -> "Print Polymorphic FOL"
    LintPolyFOL      -> "Use alt-ergo to lint Polymorphic FOL"
    PrintProps       -> "Print properties"
    PrintDefinitions -> "Print definitions translated to QuickSpec eqns"
    PrintCallGraph   -> "Print the call graph"
    PrintAutoSig     -> "Print generated signature"
    DebugAutoSig     -> "Print information about generated signature"
    DebugStrConv     -> "Print string conversions in signature"
    PrintEqClasses   -> "Print initial equivalence classes from QuickSpec"
    TranslateOnly    -> "Stop after translating"
    QuickSpecOnly    -> "Stop after QuickSpec"

-- | Makes a nice flag from a constructor string
--   e.g. PrintPolyFOL becomes print-poly-fol
flagifyString :: String -> String
flagifyString
    = map toLower . intercalate "-"
    . split (condense $ dropInitBlank $ keepDelimsL $ whenElt isUpper)

flagify :: Show a => a -> String
flagify = flagifyString . show

data Technique = Induction | Plain
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
#ifdef SUPPORT_JSON
    , json                :: Maybe FilePath
#endif

    , processes           :: Int
    , timeout             :: Double

    , isolate             :: Bool
    , only_user_stated    :: Bool
    , only                :: [String]
    , tr_mod              :: Bool
    , success             :: SuccessOpt

    , techniques          :: [Technique]

    , provers             :: [ProverName]

    , interesting_cands   :: Bool
    , user_stated_first   :: Bool
    , explore_theory      :: Bool
    , auto                :: Bool
    , extra_trans         :: [String]
    , extra               :: [String]
    , pvars               :: Bool
    , quick_check_size    :: Int
    , tests               :: Int
    , size                :: Int

    , swap_repr           :: Bool
    , quadratic           :: Bool
    , prepend_pruned      :: Bool
    , assoc_important     :: Bool
    , call_graph          :: Bool

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
    = fix_stdin
    . fix_empty_provers
    . fix_empty_techniques {- . fix_smt_data_types -}
  where
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
#ifdef SUPPORT_JSON
    , json                = Nothing &= typFile   &= help "File to write statistics to (in json format)"
#endif
    , only                = []                   &= help "Only try these user properties (affects --auto)"
    , tr_mod              = False                &= help "Unconditonally translate all module bindings"
    , success             = CleanRun             &= help "Specify what to give exit code 0"

    , auto                = False   &= groupname "\nSignature generation settings"
                                    &= name "a" &= help "Make signature with functions in user properties"
    , extra               = []                  &= help "Additional functions to add to the signature"
    , extra_trans         = []                  &= help "Like --extra, but transitively"
    , pvars               = False               &= help "Use pvars instead of vars in the auto signature"
    , quick_check_size    = 20                  &= help "Set the withQuickCheckSize (default 20)"
    , tests               = 100                 &= help "Set the withTests          (default 100)"
    , size                = 1000                &= help "Set the withSize           (default \"unlimited\")"

    , processes           = 2    &= groupname "\nProving settings"
                                 &= name "N" &= help "Prover processes          (default 2)"
    , timeout             = 1    &= name "t" &= help "Prover timeout in seconds (default 1.0)"

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

    , interesting_cands   = False   &= groupname "\nEquation ordering"
                                    &= name "i" &= help "Add interesting candidates after theorems"

    , explore_theory      = False   &= name "e"  &= help "Print explored theory"

    , user_stated_first   = False   &= name "U" &= help "Put user stated properties first in the loop"

    , swap_repr           = False   &= groupname "\nEquation ordering"
                                    &= name "s" &= help "Swap equations with their representative"
    , prepend_pruned      = False   &= name "r" &= help "Add nice pruned equations in front of queue"
    , quadratic           = False   &= name "q" &= help "All pairs of equations"
    , assoc_important     = False               &= help "Associativity is important, try it first"
    , call_graph          = False   &= name "c" &= name "cg" &= help "Sort equations by the call graph"

    , inddepth            = 1       &= name "d" &= groupname "\nStructural induction"
                                                &= help "Maximum depth       (default 1)"
    , indvars             = 2       &= name "v" &= help "Maximum variables   (default 2)"
    , indhyps             = 200     &= name "H" &= help "Maximum hypotheses  (default 200)"
    , indobligs           = 25      &= name "O" &= help "Maximum obligations (default 25)"

    , debug_flags = enumerate
         [ (f,debugDesc f) | f <- [minBound..maxBound] ]
         &= groupname "\nDebugging"
    }
    &= summary ("\n" ++ logo ++ "\n            hipspec v3.0 by Dan Rosén, danr@chalmers.se")
    &= program "hipspec"

enumerate :: (Show val,Data val) => [(val,String)] -> [val]
enumerate xs = enum $
    [] &= ignore :
    [ [x] &= name (flagify x) &= help h | (x,h) <- xs ]

whenFlag :: Monad m => Params -> DebugFlag -> m () -> m ()
whenFlag p flg = when (flg `elem` debug_flags p)

logo :: String
logo = map (\ x -> if x == 'z' then '\"' else x) $ unlines
    [ "      888      d8b                                               "
    , "      888      Y8P                                               "
    , "      888                                                        "
    , "      888888b. 888 88888b.  .d8888b  88888b.   .d88b.  .d8888    "
    , "      888  888 888 888 z88b 88K      888 z88b d8P  Y8 d8P        "
    , "      888  888 888 888  888 zY8888b. 888  888 8888888 888        "
    , "      888  888 888 888 d88P      X88 888 d88P Y8b.    Y8b.       "
    , "      888  888 888 88888Pz   88888P' 88888Pz   zY8888  zY8888    "
    , "                   888               888                         "
    , "                   888               888    zUpp till bevis!z    "
    ]

