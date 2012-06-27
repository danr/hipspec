{-
   Command Line Parameter Options

   Uses Neil Mitchell's cmdargs

   In this file it is OK to have lines with >80 characters
-}
{-# LANGUAGE DeriveDataTypeable,RecordWildCards #-}
module Hip.Params where

import System.Console.CmdArgs

data Params = Params
    { files               :: [FilePath]
    , output              :: Maybe FilePath
    , z_encode_filenames  :: Bool
    , warnings            :: Bool

    , processes           :: Int
    , batchsize           :: Int
    , timeout             :: Int
    , provers             :: String
    , methods             :: String
    , consistency         :: Bool
    , isolate             :: Bool
    , fof                 :: Bool
    , comments            :: Bool
    , dont_print_unproved :: Bool

    , swap_repr           :: Bool
    , prepend_pruned      :: Bool
    , quadratic           :: Bool
    , interesting_cands   :: Bool
    , allow_eta_red       :: Bool

    , inddepth            :: Int
    , indvars             :: Int
    , indhyps             :: Int
    , indparts            :: Int

    , db_anns             :: Bool
    }
  deriving (Show,Data,Typeable)

defParams :: Params
defParams = Params
    { files               = []      &= args   &= typFile
    , warnings            = False   &= help "Show warnings from translation"
    , output              = Nothing &= name "o" &= opt "proving/" &= typDir &= help "Save tptp files in a directory (default proving/)"
    , comments            = False   &= name "C" &= help "Write comments in tptp file"
    , fof                 = False   &= name "f" &= help "Write clauses in fof rather than cnf"
    , z_encode_filenames  = False   &= name "z" &= help "z-encode filenames when saving tptp (necessary for windows)"

    , processes           = 2       &= groupname "\nProving settings"
                                    &= name "N" &= help "Prover processes (default 2)"
    , batchsize           = 2       &= name "b" &= help "Equations to process simultaneously (default 2)"
    , timeout             = 1       &= name "t" &= help "Timeout of provers in seconds (default 1)"
    , provers             = "e"     &= name "p" &= help "Provers to use (e)prover (v)ampire (V)ampire 64-bit (s)pass equino(x) (z)3 (default e)"
    , methods             = "pi"    &= name "m" &= help "Methods to use (p)lain definition equality, (i)nduction (default pi)"

    , consistency         = False   &= name "c" &= help "Add a consistency check"
    , isolate             = False   &= name "l" &= help "Isolate user props, i.e. do not use user stated properties as lemmas"
    , dont_print_unproved = False   &= name "d" &= help "Don't print unproved conjectures from QuickSpec"

    , swap_repr           = False   &= groupname "\nEquation ordering"
                                    &= name "s" &= help "Swap equations with their representative"
    , prepend_pruned      = False   &= name "r" &= help "Add nice pruned equations from in front"
    , quadratic           = False   &= name "q" &= help "All pairs of equations"
    , interesting_cands   = False   &= name "i" &= help "Add interesting candidates after theorems"
    , allow_eta_red       = False   &= name "e" &= help "Allow eta-reduced terms"

    , inddepth            = 1       &= groupname "\nStructural induction"
                                    &= help "Maximum depth                   (default 1)"
    , indvars             = 1       &= help "Maximum variables               (default 1)"
    , indhyps             = 200     &= help "Maximum hypotheses              (default 200)"
    , indparts            = 10      &= help "Maximum parts (bases and steps) (default 10)"


    , db_anns             = False   &= groupname "\nDebugging"
                                    &= help "Debug ANN pragmas"
    }
    &= summary ("\nHipSpec v0.2.1 Dan Rosén danr@student.gu.se" ++
                "\nQuickSpec by Nicholas Smallbone nicsma@chalmers.se" ++
                "\n             and Koen Claessen koen@chalmers.se")
    &= program "hipspec"
