{-
   Command Line Parameter Options

   Uses Neil Mitchell's cmdargs

   In this file it is OK to have lines with >80 characters
-}
{-# LANGUAGE DeriveDataTypeable,RecordWildCards #-}
module HipSpec.Params where

import System.Console.CmdArgs
import HipSpec.ATP.Provers

data Params = Params
    { file                :: FilePath
    , output              :: Maybe FilePath
    , verbosity           :: Int
    , no_colour           :: Bool
    , reverse_video       :: Bool
    , z_encode_filenames  :: Bool
    , json                :: Maybe FilePath

    , processes           :: Int
    , batchsize           :: Int
    , timeout             :: Double
    , provers             :: String
    , methods             :: String
    , consistency         :: Bool
    , isolate             :: Bool
    , only_user_stated    :: Bool
    , explore_theory      :: Bool

    , case_lift_inner     :: Bool
    , var_scrut_constr    :: Bool
    , smt_data_types      :: Bool
    , bottoms             :: Bool

    , swap_repr           :: Bool
    , prepend_pruned      :: Bool
    , quadratic           :: Bool
    , interesting_cands   :: Bool
    , assoc_important     :: Bool

    , inddepth            :: Int
    , indvars             :: Int
    , indhyps             :: Int
    , indobligs           :: Int

    , permissive_junk     :: Bool
    , db_str_marsh        :: Bool
    , db_names            :: Bool
    , db_core_lint        :: Bool
    , dump_core           :: Bool
    , dump_props          :: Bool
    , dump_defns          :: Bool
    , dump_types          :: Bool
    , dump_subthys        :: Bool
    }
  deriving (Show,Data,Typeable)

-- | If you are using a theorem prover that cannot stdin then put on output.
--
--   We cannot have --smt-data-types when using --bottoms.
sanitizeParams :: Params -> Params
sanitizeParams = fix_stdin . fix_smt_data_types
  where
    fix_stdin params
        | any proverCannotStdin provers' = params
            { output = if output params == Nothing
                           then Just "proving"
                           else output params
            }
        | otherwise = params
      where
        provers' = proversFromString (provers params)

    fix_smt_data_types params
        | bottoms params && smt_data_types params = params
            { smt_data_types = False }
        | otherwise = params


defParams :: Params
defParams = Params
    { file                = ""      &= argPos 0  &= typFile
    , output              = Nothing &= name "o"  &= opt "proving" &= typDir &= help "Save tptp files in a directory"
    , verbosity           = 100                  &= help "Verbosity"
    , no_colour           = False                &= help "Don't print in colour"
    , reverse_video       = False   &= name "rv" &= help "Reverse video (i.e. assume that the terminal background is black)"
    , z_encode_filenames  = False   &= name "z"  &= help "z-encode filenames when saving tptp (necessary for windows)"
    , json                = Nothing &= typFile   &= help "File to write statistics to (in json format)"

    , processes           = 2    &= groupname "\nProving settings"
                                 &= name "N" &= help "Prover processes (default 2)"
    , batchsize           = 1    &= name "B" &= help "Equations to process simultaneously (default 1)"
    , timeout             = 1    &= name "t" &= help "Timeout of provers in seconds (default 1.0)"
    , provers             = "z"  &= name "p" &= help "Provers to use: (z)3 (Z)3 with unsat cores (default z)"
    , methods             = "pia"            &= help "Methods to use (p)lain definition equality, (i)nduction, (a)pproximation lemma (default all)"
    , explore_theory      = False   &= name "e"  &= help "Print explored theory"

    , consistency         = False   &= name "c" &= help "Add a consistency check"
    , isolate             = False   &= name "l" &= help "Isolate user props, i.e. do not use user stated properties as lemmas"
    , only_user_stated    = False   &= name "u"  &= help "Stop when all user stated properties are proved"

    , case_lift_inner     = False   &= groupname "\nTranslation settings"
                                    &= help "Lift all inner cases to top level"
    , var_scrut_constr    = False   &= help "Make a constraint instead of inlining var scrutinees"
    , smt_data_types      = False   &= help "Use SMT data types instead of own axiomatization (cannot be combined with --bottoms)"
    , bottoms             = False   &= name "b"  &= help "Add bottoms"


    , swap_repr           = False   &= groupname "\nEquation ordering"
                                    &= name "s" &= help "Swap equations with their representative"
    , prepend_pruned      = False   &= name "r" &= help "Add nice pruned equations from in front"
    , quadratic           = False   &= name "q" &= help "All pairs of equations"
    , interesting_cands   = False   &= name "i" &= help "Add interesting candidates after theorems"
    , assoc_important     = False   &= name "a" &= help "Associativity is important, try it first"

    , inddepth            = 1   &= name "d" &= groupname "\nStructural induction"
                                            &= help "Maximum depth (default 1)"
    , indvars             = 2   &= name "v" &= help "Maximum variables (default 2)"
    , indhyps             = 200 &= name "H" &= help "Maximum hypotheses (default 200)"
    , indobligs           = 25  &= name "O" &= help "Maximum obligations (default 25)"

    , db_str_marsh        = False   &= groupname "\nDebugging"
                                    &= help "Debug string marshallings (QuickSpec Strings -> GHC Core representations)"
    , db_core_lint        = False   &= help "Run core lint"
    , db_names            = False   &= help "Print names in scope"
    , dump_core           = False   &= help "Dump core bindings from the starting module"
    , dump_props          = False   &= help "Dump bindings that are considered properties"
    , dump_defns          = False   &= help "Dump bindings that are considered definitions"
    , dump_types          = False   &= help "Dump types of bindings"
    , dump_subthys        = False   &= help "Dump subtheories"
    , permissive_junk     = False   &= help "Add a lot of (seemingly) unnecessary junk. Use this if a definition doesn't get translated that should be, and file a bug report."
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
    \            hipspec v0.6 by Dan Rosén, danr@chalmers.se   \n"
    &= program "hipspec"

