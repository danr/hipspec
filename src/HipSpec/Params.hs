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
    { files               :: [FilePath]
    , output              :: Maybe FilePath
    , z_encode_filenames  :: Bool
    , warnings            :: Bool
    , json                :: Maybe FilePath
    , definitions         :: Bool
    , explore_theory      :: Bool

    , processes           :: Int
    , batchsize           :: Int
    , timeout             :: Int
    , provers             :: String
    , methods             :: String
    , readable_tptp       :: Bool
    , consistency         :: Bool
    , isolate             :: Bool
    , fof                 :: Bool
    , comments            :: Bool
    , dont_print_unproved :: Bool
    , min                 :: Bool

    , case_lift_inner     :: Bool
    , var_scrut_constr    :: Bool

    , swap_repr           :: Bool
    , prepend_pruned      :: Bool
    , quadratic           :: Bool
    , interesting_cands   :: Bool
    , assoc_important     :: Bool
    , quickspec           :: Bool

    , inddepth            :: Int
    , indvars             :: Int
    , indhyps             :: Int
    , indparts            :: Int

    , permissive_junk     :: Bool

    , db_str_marsh        :: Bool
    , dump_props          :: Bool
    , dump_defns          :: Bool
    , dump_types          :: Bool
    , dump_subthys        :: Bool
    }
  deriving (Show,Data,Typeable)

-- | If you are using a theorem prover that cannot stdin,
--   then put on output and z-encoding of filenames
sanitizeParams :: Params -> Params
sanitizeParams params
    | any proverCannotStdin (proversFromString (provers params))
        = params
            { z_encode_filenames = True
            , output = if output params == Nothing
                           then Just "proving"
                           else output params
            }
    | otherwise = params

defParams :: Params
defParams = Params
    { files               = []      &= args   &= typFile
    , warnings            = False   &= help "Show warnings from translation"
    , output              = Nothing &= name "o" &= opt "proving" &= typDir &= help "Save tptp files in a directory (default proving)"
    , comments            = False   &= name "C" &= help "Write comments in tptp file"
    , fof                 = False   &= name "f" &= help "Write clauses in fof rather than cnf"
    , z_encode_filenames  = False   &= name "z" &= help "z-encode filenames when saving tptp (necessary for windows)"
    , json                = Nothing &= help "File to write statistics to (in json format)"
    , definitions         = False   &= name "d" &= help "Print translated QuickSpec function definitions"
    , explore_theory      = False   &= name "e" &= help "Print explored theory"

    , processes           = 2       &= groupname "\nProving settings"
                                    &= name "N" &= help "Prover processes (default 2)"
    , batchsize           = 1       &= name "b" &= help "Equations to process simultaneously (default 1)"
    , timeout             = 1       &= name "t" &= help "Timeout of provers in seconds (default 1)"
    , provers             = "e"     &= name "p" &= help "Provers to use: (e)prover eproo(f) eprover(w)indows (v)ampire (s)pass equino(x) (z)3 (p)aradox, any other in upper case is rally paradox and the lower case version"
    , methods             = "pi"                &= help "Methods to use (p)lain definition equality, (i)nduction (default pi)"
    , readable_tptp       = False   &= name "R" &= help "Disable quicker generation of TPTP with variable names from Uniques. Uses cnf and $min and writes no comments."

    , consistency         = False   &= name "c" &= help "Add a consistency check"
    , isolate             = False   &= name "l" &= help "Isolate user props, i.e. do not use user stated properties as lemmas"
    , dont_print_unproved = False   &= name "u" &= help "Don't print unproved conjectures from QuickSpec"
    , min                 = False   &= name "m" &= help "Use min and minrec translation"

    , case_lift_inner  = False &= groupname "\nTranslation settings"
                               &= help "Lift all inner cases to top level"
    , var_scrut_constr = False &= help "Make a constraint instead of inlining var scrutinees"


    , swap_repr           = False   &= groupname "\nEquation ordering"
                                    &= name "s" &= help "Swap equations with their representative"
    , prepend_pruned      = False   &= name "r" &= help "Add nice pruned equations from in front"
    , quadratic           = False   &= name "q" &= help "All pairs of equations"
    , interesting_cands   = False   &= name "i" &= help "Add interesting candidates after theorems"
    , assoc_important     = False   &= name "a" &= help "Associativity is important, try it first"
    , quickspec           = False   &= name "Q" &= help "Print conjectures from QuickSpec"

    , inddepth            = 1       &= name "D" &= groupname "\nStructural induction"
                                    &= help "Maximum depth                   (default 1)"
    , indvars             = 1       &= name "S" &= help "Maximum variables               (default 1)"
    , indhyps             = 200     &= name "H" &= help "Maximum hypotheses              (default 200)"
    , indparts            = 10      &= name "P" &= help "Maximum parts (bases and steps) (default 10)"


    , db_str_marsh        = False   &= groupname "\nDebugging"
                                    &= help "Debug string marshallings (QuickSpec Strings -> GHC Core representations)"
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
    \       hipspec v0.3.2 by Dan Rosén, danr@student.chalmers.se   \n"
    &= program "hipspec"
