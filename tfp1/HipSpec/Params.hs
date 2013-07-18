{-
   Command Line Parameter Options

   Uses Neil Mitchell's cmdargs

   In this file it is OK to have lines with >80 characters
-}
{-# LANGUAGE DeriveDataTypeable #-}
module HipSpec.Params
    ( Params(..)
    , defParams
    , sanitizeParams
    , cmdArgs
    , DebugFlag(..)
    , Technique(..)
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
--    = PrintRich
    = PrintSimple
--    | PrintFunFO
    | PrintPolyFOL
    | PrintProps
    | PrintCallGraph
    | PrintAutoSig
    | DebugAutoSig
    | DebugScope
    | DebugStrConv
    | PrintEqClasses
    | TranslateOnly
  deriving (Eq,Ord,Show,Enum,Bounded,Data,Typeable)

defStr :: Eq a => a -> [a] -> String
defStr x xs | x `elem` xs = " (default)"
             | otherwise   = ""

-- | Descrptions of debug flags
debugDesc :: DebugFlag -> String
debugDesc flg = case flg of
--    PrintRich      -> "Print Rich IR"
    PrintSimple    -> "Print Simple IR"
--    PrintFunFO     -> "Print First-Order Functional IR"
    PrintPolyFOL   -> "Print Polymorphic FOL"
    PrintProps     -> "Print properties"
    PrintCallGraph -> "Print the call graph"
    PrintAutoSig   -> "Print generated signature"
    DebugAutoSig   -> "Print debug information about generated signature"
    DebugScope     -> "Print names in scope"
    DebugStrConv   -> "Print debug information about string conversions in QuickSpec signature"
    PrintEqClasses -> "Print initial equivalence classes from QuickSpec"
    TranslateOnly  -> "Stop after translating"

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

defTechs :: [Technique]
defTechs = [Induction,Plain]

-- | Parameters
data Params = Params
    { file                :: FilePath
    , output              :: Maybe FilePath
    , verbosity           :: Int
    , no_colour           :: Bool
    , reverse_video       :: Bool
    , z_encode_filenames  :: Bool
    , json                :: Maybe FilePath

    , processes           :: Int
    , timeout             :: Double

    , isolate             :: Bool
    , only_user_stated    :: Bool
    , techniques          :: [Technique]

    , provers             :: [ProverName]

    , interesting_cands   :: Bool
    , only                :: [String]

--     , consistency         :: Bool
    , user_stated_first   :: Bool
    , explore_theory      :: Bool
    , auto                :: Bool
    , extra_trans         :: [String]
    , extra               :: [String]
    , pvars               :: Bool
    , quick_check_size    :: Int
    , tests               :: Int
    , size                :: Int

{-
    , smt_data_types      :: Bool
    , bottoms             :: Bool
-}


    , swap_repr           :: Bool
    , quadratic           :: Bool
    , prepend_pruned      :: Bool
    , assoc_important     :: Bool
    , call_graph          :: Bool

    , inddepth            :: Int
    , indvars             :: Int
    , indhyps             :: Int
    , indobligs           :: Int

{-
    , db_str_marsh        :: Bool
    , db_names            :: Bool
    , db_core_lint        :: Bool
    , dump_sig            :: Bool
    , dump_auto_sig       :: Bool
    , dump_auto_info      :: Bool
    , dump_call_graph     :: Bool
    , dump_core           :: Bool
    , dump_props          :: Bool
    , dump_eqclasses      :: Bool
    , debug               :: Bool
    -}

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
        | null (techniques params) = params { techniques = defTechs }
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
    , output              = Nothing &= name "o"  &= opt "proving" &= typDir &= help "Save tptp files in a directory"
    , verbosity           = 100                  &= help "Verbosity"
    , no_colour           = False                &= help "Don't print in colour"
    , reverse_video       = False   &= name "rv" &= help "Reverse video (i.e. assume that the terminal background is black)"
    , z_encode_filenames  = False   &= name "z"  &= help "z-encode filenames when saving tptp (necessary for windows)"
    , json                = Nothing &= typFile   &= help "File to write statistics to (in json format)"
    , only                = []                  &= help "Only try to prove these properties (also affects --auto)"

    , auto                = False   &= groupname "\nSignature settings"
                                    &= name "a" &= help "Automatically make signature from the functions used in properties (transitively)"
    , extra               = []                  &= help "Functions to add to the signature that cannot be found from the properties"
    , extra_trans         = []                  &= help "Like --extra, but also add the functions (and constructors) it calls (transitively)"
    , pvars               = False               &= help "Use pvars instead of vars in the --auto signature"
    , quick_check_size    = 20                  &= help "Set the withQuickCheckSize in the --auto signature (default 20)"
    , tests               = 100                 &= help "Set the withTests in the --auto signature (default 100)"
    , size                = 1000                &= help "Set the withSize in the --auto signature (default \"unlimited\")"

    , processes           = 2    &= groupname "\nProving settings"
                                 &= name "N" &= help "Prover processes (default 2)"
    , timeout             = 1    &= name "t" &= help "Timeout of provers in seconds (default 1.0)"
    , techniques = enum $
         ( [] &= ignore ) :
         [ [t] &= name (flagify t) &= help (show t ++ " (default)")
         | t <- [minBound..maxBound]
         ]

    , provers = enum
        (( [] &= ignore ) :
         [ [pn] &= name (flagify pn) &= help (prover_desc p ++ defStr pn defaultProverNames)
         | pn <- allProverNames
         , let p = proverFromName pn
         ])
         &= groupname "\nBackends (may select multiple)"

    , isolate             = False   &= name "l" &= help "Isolate user props, i.e. do not use user stated properties as lemmas"
    , only_user_stated    = False   &= name "u" &= help "Stop when all user stated properties are proved"

    , interesting_cands   = False   &= groupname "\nEquation ordering"
                                    &= name "i" &= help "Add interesting candidates after theorems"

    , explore_theory      = False   &= name "e"  &= help "Print explored theory"

    , user_stated_first   = False   &= name "U" &= help "Put user stated properties first in the loop"

--    , consistency         = False   &= name "C" &= help "Add a consistency check (try to prove false)"

{-
    , smt_data_types      = False   &= help "Use SMT data types instead of own axiomatization (cannot be combined with --bottoms)"
    , bottoms             = False   &= name "b"  &= help "Add bottoms"
-}

    , swap_repr           = False   &= groupname "\nEquation ordering"
                                    &= name "s" &= help "Swap equations with their representative"
    , prepend_pruned      = False   &= name "r" &= help "Add nice pruned equations from in front"
    , quadratic           = False   &= name "q" &= help "All pairs of equations"
    , assoc_important     = False               &= help "Associativity is important, try it first"
    , call_graph          = False   &= name "c" &= name "cg" &= help "Sort equations by the call graph"

    , inddepth            = 1       &= name "d" &= groupname "\nStructural induction"
                                                &= help "Maximum depth (default 1)"
    , indvars             = 2       &= name "v" &= help "Maximum variables (default 2)"
    , indhyps             = 200     &= name "H" &= help "Maximum hypotheses (default 200)"
    , indobligs           = 25      &= name "O" &= help "Maximum obligations (default 25)"

    , debug_flags         = enum
        ([] &= ignore :
         [ [f] &= name (flagify f) &= help (debugDesc f)
         | f <- [minBound..maxBound]
         ])
       &= groupname "\nDebugging"

    {-
                                    &= help "Debug string marshallings (QuickSpec Strings -> GHC Core representations)"
    , db_core_lint        = False   &= help "Run core lint"
    , db_names            = False   &= help "Print names in scope"
    , dump_sig            = False   &= help "Print the signature used"
    , dump_auto_sig       = False   &= help "Print the signature generated by --auto"
    , dump_auto_info      = False   &= help "Print some information generated by --auto"
    , dump_call_graph     = False   &= help "Print the QuickSpec signature's call graph"
    , dump_core           = False   &= help "Print core bindings when obtained and translated"
    , dump_props          = False   &= help "Print bindings that are considered properties"
    , dump_eqclasses      = False   &= help "Print the equivalence classes from QuickSpec"
    , debug               = False   &= help "Write various debug messages"
    -}
    }
    &= summary "\n\
    \      888      d8b                                             \n\
    \      888      Y8P                                             \n\
    \      888                                                      \n\
    \      888888b. 888 88888b.  .d8888b  88888b.   .d88b.  .d8888  \n\
    \      888  888 888 888 \"88b 88K      888 \"88b d8P  Y8 d8P      \n\
    \      888  888 888 888  888 \"Y8888b. 888  888 8888888 888      \n\
    \      888  888 888 888 d88P      X88 888 d88P Y8b.    Y8b.     \n\
    \      888  888 888 88888P\"   88888P' 88888P\"   \"Y8888  \"Y8888  \n\
    \                   888               888                       \n\
    \                   888               888                       \n\
    \\n\
    \            hipspec v3.0 by Dan Rosén, danr@chalmers.se   \n"
    &= program "hipspec"

whenFlag :: Monad m => Params -> DebugFlag -> m () -> m ()
whenFlag p flg = when (flg `elem` debug_flags p)


