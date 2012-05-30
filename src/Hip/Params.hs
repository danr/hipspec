{-# LANGUAGE DeriveDataTypeable,RecordWildCards #-}
module Hip.Params where

import System.Console.CmdArgs

data Params = Params { files           :: [FilePath]
                     , latex           :: Bool
                     , output          :: Maybe FilePath
                     , warnings        :: Bool
                     , statistics      :: Bool

                     , isolate_user_props :: Bool

                     , processes       :: Int
                     , batchsize       :: Int
                     , timeout         :: Int
                     , provers         :: String
                     , methods         :: String
                     , reprove         :: Bool
                     , consistency     :: Bool

                     , cnf             :: Bool

                     , ord_swap        :: Bool
                     , ord_prep_pruned :: Bool
                     , ord_quadratic   :: Bool
                     , ord_dep_sort    :: Bool

                     , dont_print_unproved  :: Bool

                     , inddepth        :: Int
                     , indvars         :: Int
                     , indhyps         :: Int
                     , indsteps        :: Int

                     , thy_no_exteq       :: Bool
                     , thy_no_typreds     :: Bool
                     , thy_no_infdom      :: Bool

                     , fpimax          :: Int

                     , tptp            :: Bool
                     , core            :: Bool
                     , dbfh            :: Bool
                     , dbfol           :: Bool
                     , dbproof         :: Bool
                     }
  deriving (Show,Data,Typeable)

showParams :: Params -> String
showParams Params{..} = " timeout: "  ++ show timeout ++
                        " provers: "  ++ provers ++
                        " methods: "  ++ methods ++
                        " reprove: "  ++ show reprove ++
                        " inddepth: " ++ show inddepth ++
                        " indvars: "  ++ show indvars ++
                        " indsteps: " ++ show indsteps ++
                        " fpimax: "   ++ show fpimax

defParams :: Params
defParams = Params
  { files       = []      &= args &= typFile
  , latex       = False   &= help "Generate latex output (currently unsupported)"
  , warnings    = False   &= help "Show warnings from translation"
  , output      = Nothing &= opt  "proving/" &= typDir &= help "Output all tptp files in a directory (default proving/)"
  , statistics  = False   &= help "Generate statistics files (run with --reprove)"

  , isolate_user_props = False &= help "Isolate user props, i.e. do not use user stated properties as lemmas"

  , processes   = 2       &= help "Number of prover processes (default 2)" &= name "p" &= groupname "\nProving settings"
  , batchsize   = 0       &= ignore
  , timeout     = 1       &= help "Timout of provers in seconds (default 1)" &= name "t"
  , provers     = "e"     &= help "Provers to use (e)prover (v)ampire (p)rover9 (s)pass equino(x)"
  , methods     = "pisfa" &= help "Methods to use (p)lain (i)nduction (s)tructural (f)ixpoint (a)pprox"
  , reprove     = False   &= help "Reprove theorems already known to be true"
  , consistency = False   &= help "Try to prove the consistency a file's generated theory"

  , cnf         = False   &= help "Output in cnf"

  , ord_swap        = False &= ignore
  , ord_prep_pruned = False &= ignore
  , ord_quadratic   = False &= ignore
  , ord_dep_sort    = False &= ignore

  , dont_print_unproved  = False &= ignore

  , thy_no_exteq    = False &= help "Extensional equality of pointers (completness)"            &= name "ne" &= groupname "Theory properties"
  , thy_no_typreds  = False &= help "Typing predicates of potentially finite types (soundness)" &= name "nt"
  , thy_no_infdom   = False &= help "Domain axioms for infinite types (completeness)"           &= name "ni"

  , inddepth    = 1       &= help "Max depth to do structural induction (default 1)" &= groupname "\nStructural induction"
  , indvars     = 1       &= help "Number of variables to do structural induction on (default 1)"
  , indhyps     = 200     &= help "Maximum number of hypotheses from structural induction (default 200)"
  , indsteps    = 10      &= help "Maximum number of step cases from structural induction (default 10)"

  , fpimax      = 25      &= help "Maximum number of lifted functions (default 25)" &= groupname "\nFixpoint induction"

  , tptp        = False   &= help "Generate tptp output and terminate" &= name "f"  &= groupname "\nDebug"
  , core        = False   &= help "Translate hs to core and terminate" &= name "c"
  , dbfh        = False   &= help "Print debug output of Haskell -> Core translation"
  , dbfol       = False   &= help "Print debug output of Core -> FOL"
  , dbproof     = False   &= help "Print debug output when making proofs"
  }
  &= summary "hipspec v0.1 Dan Rosén danr@student.gu.se"
  &= program "hipspec"
  &= verbosity


hipSpecParams :: String -> Params
hipSpecParams file = Params
  { files       = []      &= ignore
  , latex       = False   &= ignore -- help "Generate latex output (currently unsupported)"
  , warnings    = False   &= help "Show warnings from translation"
  , output      = Nothing &= opt  "proving/" &= typDir &= help "Output all tptp files in a directory (default proving/)" &= name "o"
  , statistics  = False   &= ignore -- help "Generate statistics files (run with --reprove)"

  , isolate_user_props = False &= help "Isolate user props, i.e. do not use user stated properties as lemmas" &= name "isolate" &= name "i"

  , processes   = 2       &= help "Number of prover processes (default 2)" &= name "p" &= groupname "\nProving settings"
  , batchsize   = 2       &= help "Number of equations to process simultaneously (default 2)" &= name "b"
  , timeout     = 1       &= help "Timout of provers in seconds (default 1)" &= name "t"
  , provers     = "sev"   &= help "Provers to use (e)prover (v)ampire (V)ampire64 (p)rover9 (s)pass equino(x)"
  , methods     = "pisfa" &= ignore -- help "Methods to use (p)lain (i)nduction (s)tructural (f)ixpoint (a)pprox"
  , reprove     = False   &= help "Reprove theorems already known to be true"
  , consistency = False   &= help "Add a consistency check (default: off)" &= name "c"

  , cnf         = False   &= help "Output in cnf"

  , ord_swap        = False &= help "Swap equations with their representative" &= name "swap" &= groupname "\nQuickSpec equation ordering"
  , ord_prep_pruned = False &= help "Add nice pruned equations from QuickSpec in front of all equations" &= name "prepend-pruned"
  , ord_quadratic   = False &= help "Add quadratic number of equations instead of linear" &= name "quadratic"
  , ord_dep_sort    = False &= help "Sort equations by function dependency ordering" &= name "dep-sort"

  , dont_print_unproved  = False &= help "Don't print unproved equations from QuickSpec"

  , thy_no_exteq    = False &= help "Extensional equality of pointers (completness)"            &= name "ne" &= groupname "Theory properties"
  , thy_no_typreds  = False &= help "Typing predicates of potentially finite types (soundness)" &= name "nt"
  , thy_no_infdom   = False &= help "Domain axioms for infinite types (completeness)"           &= name "ni"

  , inddepth    = 1       &= help "Max depth to do structural induction (default 1)" &= groupname "\nStructural induction"
  , indvars     = 1       &= help "Number of variables to do structural induction on (default 1)"
  , indhyps     = 200     &= help "Maximum number of hypotheses from structural induction (default 200)"
  , indsteps    = 10      &= help "Maximum number of step cases from structural induction (default 10)"

  , fpimax      = 25      &= ignore -- help "Maximum number of lifted functions (default 25)" &= groupname "\nFixpoint induction"

  , tptp        = False   &= help "Generate tptp output and terminate" &= name "f"  &= groupname "\nDebug"
  , core        = False   &= help "Translate hs to core and terminate" &= name "C"
  , dbfh        = False   &= help "Print debug output of Haskell -> Core translation"
  , dbfol       = False   &= help "Print debug output of Core -> FOL"
  , dbproof     = False   &= help "Print debug output when making proofs"
  }
  &= summary ("HipSpec on " ++ file ++
              "\n\nHipSpec v0.1 Dan Rosén danr@student.gu.se" ++
              "\nQuickSpec by Nicholas Smallbone nicsma@chalmers.se" ++
              "\n             and Koen Claessen koen@chalmers.se")
  &= verbosity

