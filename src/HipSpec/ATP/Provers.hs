module HipSpec.ATP.Provers where

import HipSpec.ATP.Results

import Data.Maybe
import Data.Char
import Data.List
import Data.List.Split

data TheoryType = TPTP | SMT | SMTUnsatCore
  deriving (Eq,Ord,Show)

data ProverName
    = E
    | Eproof
    | Equinox
    | Paradox
    | SPASS
    | Vampire
    | Z3
    | Z3UnsatCores
  deriving (Eq,Ord)

instance Show ProverName where
    show E            = "eprover"
    show Eproof       = "eproof"
    show Equinox      = "equinox"
    show Paradox      = "paradox"
    show SPASS        = "spass"
    show Vampire      = "vampire"
    show Z3           = "z3"
    show Z3UnsatCores = "z3"

proverCanSpecifyLemmas :: Prover -> Bool
proverCanSpecifyLemmas = isJust . proverParseLemmas

data Prover = Prover
    { proverName          :: ProverName
    -- ^ Name of the prover in the prover datatype
    , proverCmd           :: String
    -- ^ system command to createProcess
    , proverCannotStdin   :: Bool
    -- ^ this prover cannot read from stdin, so instead read from file
    , proverArgs          :: String -> Double -> [String]
    -- ^ given file name (if proverCannotStdin)
    --   and timeout in secs, args to createProcess
    , proverProcessOutput :: String  -> ProverResult
    -- ^ processes the output and time and gives a result
    , proverShort         :: Char
    -- ^ short char for command line options
    , proverSuppressErrs  :: Bool
    -- ^ should we ignore standard error from this prover?
    , proverParseLemmas   :: Maybe (String -> [Int])
    -- ^ this prover's method of parsing lemmas
    , proverTheoryType    :: TheoryType
    }

-- | A template for most provers:
--      * Can read from stdin
--      * Uses SZS status reporting
--      * Only raises errors upon real errors
--      * Cannot parse lemmas
template :: Prover
template = Prover
    { proverName          = error "stdProver: Fill in your prover's name"
    , proverCmd           = error "stdProver: Fill in your prover's cmd"
    , proverCannotStdin   = False
    , proverArgs          = error "stdProver: Fill in your prover's args"
    , proverProcessOutput = searchOutput statusSZS
    , proverShort         = error "stdProver: Fill in your prover's short"
    , proverSuppressErrs  = False
    , proverParseLemmas   = Nothing
    , proverTheoryType    = TPTP
    }

-- Should really use something more efficient than isInfixOf
searchOutput :: [(String,ProverResult)] -> String -> ProverResult
-- searchOutput _          ""     = Failure
searchOutput []         output = Unknown output
searchOutput ((s,r):xs) output
    | s `isInfixOf` output = r
    | otherwise            = searchOutput xs output


statusSZS :: [(String,ProverResult)]
statusSZS =
    [("Theorem",mkSuccess)
    ,("Unsatisfiable",mkSuccess)
    ,("CounterSatisfiable",Failure)
    ,("Satisfiable",Failure)
    ,("Timeout",Failure)
    ,("ResourceOut",Failure)
    ]

allProvers :: [Prover]
allProvers =
    [eprover
    ,eproof
    ,eprover_win
    ,equinox
    ,paradox
    ,spass
    ,vampire
    ,z3smt
    ,z3tptp
    ]

proversFromString :: String -> [Prover]
proversFromString = mapMaybe (\ c -> lookup c shorts)
  where
    shorts = [ (proverShort p,p) | p <- allProvers ]

showCeil :: Double -> String
showCeil = show . (ceiling :: Double -> Integer)

eprover :: Prover
eprover = template
    { proverName          = E
    , proverCmd           = "eprover"
    , proverArgs          = \ _ t -> words $ "-tAuto -xAuto --tptp3-format -s --cpu-limit=" ++ showCeil t
    , proverShort         = 'e'
    }

eprover_win :: Prover
eprover_win = eprover
    { proverCmd           = "eprover.exe"
    , proverShort         = 'w'
    , proverSuppressErrs  = True
    }

eproof :: Prover
eproof = template
    { proverName          = Eproof
 -- , proverCmd           = "eproof"
 -- , proverArgs          = \s _ -> words "-tAuto -xAuto --tptp3-format" ++ [s]
 -- UGLY: eproof does not like to be terminated by us, so I use `timeout'
    , proverCmd           = "timeout"
    , proverArgs          = \ s t -> [showCeil t] ++ words "eproof -tAuto -xAuto --tptp3-format" ++ [s]
    , proverShort         = 'f'
    , proverParseLemmas   = Just lemmaParser
    , proverSuppressErrs  = True
    , proverCannotStdin   = True
    }

z3tptp :: Prover
z3tptp = template
    { proverName          = Z3UnsatCores
    , proverCmd           = "z3"
    , proverArgs          = \ _ _ -> words "-smt2 -nw /dev/stdin"
    , proverShort         = 'Z'
    , proverTheoryType    = SMTUnsatCore
    , proverProcessOutput = searchOutput [("unsat",mkSuccess),("sat",Failure)]
    , proverParseLemmas   = Just lemmaParser
    }

z3smt :: Prover
z3smt = template
    { proverName          = Z3
    , proverCmd           = "z3"
    , proverArgs          = \ _ _ -> words $ "-smt2 -nw /dev/stdin"
    , proverShort         = 'z'
    , proverTheoryType    = SMT
    , proverProcessOutput = searchOutput [("unsat",mkSuccess),("sat",Failure)]
    }

paradox :: Prover
paradox = template
    { proverName          = Paradox
    , proverCmd           = "paradox"
    , proverArgs          = \s _ -> s : words "--no-progress --tstp"
    , proverShort         = 'p'
    , proverCannotStdin   = True
    }


vampire :: Prover
vampire = template
    { proverName          = Vampire
    , proverCmd           = "vampire_lin32"
    , proverArgs          = \_ t -> words ("--proof tptp --mode casc --output_axiom_names on -t " ++ showCeil t)
    , proverShort         = 'v'
    , proverParseLemmas   = Just lemmaParser
    }

spass :: Prover
spass = template
    { proverName          = SPASS
    , proverCmd           = "SPASS"
    , proverArgs          = \_ t -> words ("-Stdin -Auto -TPTP -PGiven=0 -PProblem=0 -DocProof=1 -PStatistic=0 -TimeLimit=" ++ showCeil t)
    , proverProcessOutput = searchOutput
                                [("Proof found.",mkSuccess)
                                ,("Completion found.",Failure)
                                ,("Ran out of time.",Failure)]
    , proverShort         = 's'
    , proverParseLemmas   = Just lemmaParser
    }

equinox :: Prover
equinox = template
    { proverName          = Equinox
    , proverCmd           = "equinox"
    , proverCannotStdin   = True
    , proverArgs          = \s _ -> words ("--tstp --split " ++ s)
    , proverShort         = 'x'
    }

-- | The parser eproof uses to parse TSTP lemmas
lemmaParser :: String -> [Int]
lemmaParser = mapMaybe parseLemma . words

parseLemma :: String -> Maybe Int
parseLemma s = do
    [_,rest] <- return (splitOn "lemma_" s)
    (n_str,'_':_) <- return (break (== '_') rest)
    (n,"") <- listToMaybe (reads n_str)
    return n

