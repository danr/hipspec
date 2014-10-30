{-# LANGUAGE DeriveDataTypeable #-}
module HipSpec.ATP.Provers where

import Data.Maybe
import Data.List
import Data.Data

import HipSpec.ATP.Z3ProofParser

import HipSpec.Pretty

import System.FilePath ((<.>))

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | The names of the different supported theorem provers
data ProverName = Z3 | Z3PP | CVC4 | CVC4i | CVC4ig | AltErgo | MonoAltErgo | Vampire | E | SPASS | Equinox
  deriving (Eq,Ord,Enum,Bounded,Show,Data,Typeable)

defaultProverNames :: [ProverName]
defaultProverNames = [Z3]

proverFromName :: ProverName -> Prover
proverFromName p = case p of
    AltErgo     -> altErgo
    MonoAltErgo -> monoAltErgo
    Vampire     -> vampire
    Z3          -> z3
    Z3PP        -> z3pp
    E           -> eprover
    Equinox     -> equinox
    SPASS       -> spass
    CVC4        -> mkCVC4 p "" []
    CVC4i       -> mkCVC4 p " with induction" ["--quant-ind"]
    CVC4ig      -> mkCVC4 p " with induction and conjecture generation"
                            ["--quant-ind","--conjecture-gen","--conjecture-gen-per-round=3"]

proversFromNames :: [ProverName] -> [Prover]
proversFromNames = map proverFromName

allProverNames :: [ProverName]
allProverNames = [minBound..maxBound]

-- | A record of information concerning a theorem prover
data Prover = Prover
    { prover_cmd            :: String
    -- ^ System command to createProcess
    , prover_desc           :: String
    -- ^ Description in the parameter list
    , prover_name           :: ProverName
    -- ^ Refers to its name
    , prover_cannot_stdin   :: Bool
    -- ^ This prover cannot read from stdin, so instead read from file
    , prover_args           :: String -> Double -> [String]
    -- ^ Given file name (if prover_cannot_stdin)
    --   and timeout in secs, args to createProcess
    , prover_process_output :: String -> Maybe Res
    -- ^ Processes the output and time and gives a result
    , prover_suppress_errs  :: Bool
    -- ^ Should we ignore standard error from this prover?
    , prover_parse_lemmas   :: Maybe (String -> [Int])
    -- ^ This prover's method of parsing lemmas
    , prover_parse_proofs   :: Maybe ((String -> LogicId) -> String -> Insts)
    -- ^ Parse proofs
    , prover_input_format   :: InputFormat
    }

instance Show Prover where
    show = show . prover_name

-- | Input formats
data InputFormat
    = AltErgoFmt
    | AltErgoMonoFmt
    | MonoTFF
    | FOF
    | SMT
    | SMT_PP
    -- ^ With produce-proofs
    | SMT_CVC4
    -- ^ For CVC4: the goal is not skolemised, uninterpreted sorts are
    --   ints, and all labels and names are removed.
  deriving (Eq,Ord,Show)

completeName :: InputFormat -> FilePath -> FilePath
completeName fmt s = case fmt of
    AltErgoFmt     -> s <.> "mlw"
    AltErgoMonoFmt -> (s ++ "_m") <.> "mlw"
    MonoTFF        -> s <.> "tff"
    SMT            -> s <.> "smt"
    SMT_CVC4       -> (s ++ "_cvc4") <.> "smt"
    SMT_PP         -> (s ++ "_pp") <.> "smt"
    FOF            -> s <.> "p"

outputSZS :: [(String,Maybe Res)]
outputSZS =
    [ ("SZS status " ++ s,r)
    | (s,r) <-
        [("Unsatisfiable",proven),("Theorem",proven)
        ,("Timeout",failure),("Satisfiable",failure),("ResourceOut",failure)
        ]
    ]

eprover :: Prover
eprover = Prover
    { prover_cmd            = "eprover"
    , prover_desc           = "E prover"
    , prover_name           = E
    , prover_cannot_stdin   = False
    , prover_args           = \ _f t -> ["--auto-schedule","--tptp3-format","--silent","--cpu-limit="++showCeil t]
    , prover_process_output = searchOutput outputSZS
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = FOF
    }

equinox :: Prover
equinox = Prover
    { prover_cmd            = "equinox"
    , prover_desc           = "Equinox"
    , prover_name           = Equinox
    , prover_cannot_stdin   = False
    , prover_args           = \ _f t -> ["/dev/stdin","--tstp","--time",showCeil t,"--no-progress"]
    , prover_process_output = searchOutput outputSZS
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = FOF
    }

spass :: Prover
spass = Prover
    { prover_cmd            = "SPASS"
    , prover_desc           = "SPASS"
    , prover_name           = SPASS
    , prover_cannot_stdin   = False
    , prover_args           = \ _f t -> ["-Auto","-TPTP","-PGiven=0","-PProblem=0","-DocProof=0","-PStatistic=0","-Stdin","-TimeLimit="++showCeil t]
    , prover_process_output = searchOutput
        [("SPASS beiseite: Proof found.",proven)
        ,("SPASS beiseite: Completion found.",failure)
        ,("SPASS beiseite: Ran out of time.",failure)
        ,("No formulae and clauses found in input file!",failure)
        ]
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = FOF
    }

altErgo :: Prover
altErgo = Prover
    { prover_cmd            = "alt-ergo"
    , prover_desc           = "Alt-Ergo"
    , prover_name           = AltErgo
    , prover_cannot_stdin   = True
    , prover_args           = \ f _t -> [f,"-triggers-var"]
    , prover_process_output = searchOutput
        [("Valid",proven),("I don't know",failure) ]
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = AltErgoFmt
    }

monoAltErgo :: Prover
monoAltErgo = altErgo
    { prover_input_format = AltErgoMonoFmt
    , prover_name         = MonoAltErgo
    }

vampire :: Prover
vampire = Prover
    { prover_cmd            = "vampire_rel"
    , prover_desc           = "Vampire"
    , prover_name           = Vampire
    , prover_cannot_stdin   = True
    , prover_args           = \ f t -> [f,"-t",showCeil t,"-mode","casc"]
    , prover_process_output = searchOutput outputSZS
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = MonoTFF
    }

z3 :: Prover
z3 = Prover
    { prover_cmd            = "z3"
    , prover_desc           = "Z3"
    , prover_name           = Z3
    , prover_cannot_stdin   = False
    , prover_args           = \ _f _t -> ["-smt2","-nw","/dev/stdin"]
    , prover_process_output = searchOutput
        [("error",Just Error)
        ,("unsat",proven)
        ,("unknown",failure)
        ]
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = SMT
    }

z3pp :: Prover
z3pp = z3
    { prover_name         = Z3PP
    , prover_parse_proofs = Just z3proofParser
    , prover_input_format = SMT_PP
    }

mkCVC4 :: ProverName -> String -> [String] -> Prover
mkCVC4 name desc opts = Prover
    { prover_cmd            = "cvc4"
    , prover_desc           = "CVC4" ++ desc
    , prover_name           = name
    , prover_cannot_stdin   = False
    , prover_args           = \ _f t ->
        ["--lang=smt2","--tlimit=" ++ showCeil (t*1000)] ++
        ["--quant-cf","--full-saturate-quant"] ++
        opts
    , prover_process_output = searchOutput
        [("unsat",proven)
        ,("unknown",failure)
        ]
    , prover_suppress_errs  = False
    , prover_parse_lemmas   = Nothing
    , prover_parse_proofs   = Nothing
    , prover_input_format   = SMT_CVC4
    }

data Res = Proven | SoftFailure | Error

proven,failure :: Maybe Res
proven  = Just Proven
failure = Just SoftFailure

showCeil :: Double -> String
showCeil = show . (ceiling :: Double -> Integer)

-- Should really use something more efficient than isInfixOf
searchOutput :: [(String,Maybe Res)] -> String -> Maybe Res
searchOutput []         _      = Nothing
searchOutput ((s,r):xs) output
    | s `isInfixOf` output = r
    | otherwise            = searchOutput xs output

proverCanSpecifyLemmas :: Prover -> Bool
proverCanSpecifyLemmas = isJust . prover_parse_lemmas

