module Hip.ATP.Provers where

import Hip.ATP.Results

import Data.Maybe
import Data.Char
import Data.List
import Data.List.Split

data ProverName
    = E
    | Eproof
    | Equinox
    | Paradox
    | SPASS
    | Vampire
    | Z3
    | ParadoxAnd Prover

instance Show ProverName where
    show E              = "eprover"
    show Eproof         = "eproof"
    show Equinox        = "equinox"
    show Paradox        = "paradox"
    show (ParadoxAnd p) = "paradox and " ++ show (proverName p)
    show SPASS          = "spass"
    show Vampire        = "vampire"
    show Z3             = "z3"

data Prover = Prover
    { proverName          :: ProverName
    -- ^ Name of the prover in the prover datatype
    , proverCmd           :: String
    -- ^ system command to createProcess
    , proverCannotStdin   :: Bool
    -- ^ this prover cannot read from stdin, so instead read from file
    , proverArgs          :: String -> Int -> [String]
    -- ^ given file name (if proverCannotStdin)
    --   and timeout in secs, args to createProcess
    , proverProcessOutput :: String -> Integer -> ProverResult
    -- ^ processes the output and time and gives a result
    , proverShort         :: Char
    -- ^ short char for command line options
    , proverSuppressErrs  :: Bool
    -- ^ should we ignore standard error from this prover?
    , proverParseLemmas   :: Maybe (String -> [String])
    -- ^ this prover's method of parsing lemmas
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
    }

-- Should really use something more efficient than isInfixOf
searchOutput :: [(String,time -> ProverResult)] -> String -> time -> ProverResult
searchOutput []         output _ = Unknown output
searchOutput ((s,r):xs) output time
    | s `isInfixOf` output = r time
    | otherwise            = searchOutput xs output time


statusSZS :: [(String,Integer -> ProverResult)]
statusSZS =
    [("Theorem",mkSuccess)
    ,("Unsatisfiable",mkSuccess)
    ,("CounterSatisfiable",const Failure)
    ,("Satisfiable",const Failure)
    ,("Timeout",const Failure)
    ]

mkParadoxAnd :: Prover -> Prover
mkParadoxAnd p = template
    { proverName          = ParadoxAnd p
    , proverShort         = toUpper (proverShort p)
    , proverCannotStdin   = True
    }
  -- ^ mkParadoxAnd is deeply magical, see Hip.ATP.RunProver

allProvers :: [Prover]
allProvers = baseProvers ++ map mkParadoxAnd baseProvers

baseProvers :: [Prover]
baseProvers =
    [eprover
    ,eproof
    ,eprover_win
    ,equinox
    ,paradox
    ,spass
    ,vampire
    ,z3]

proversFromString :: String -> [Prover]
proversFromString str = filter ((`elem` str) . proverShort) allProvers

eprover :: Prover
eprover = template
    { proverName          = E
    , proverCmd           = "eprover"
    , proverArgs          = \_ _ -> words "-tAuto -xAuto --tptp3-format -s"
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
    , proverArgs          = \s t -> [show t] ++ words "eproof -tAuto -xAuto --tptp3-format" ++ [s]
    , proverShort         = 'f'
    , proverParseLemmas   = Just eproofLemmaParser
    , proverSuppressErrs  = True
    , proverCannotStdin   = True
    }

z3 :: Prover
z3 = template
    { proverName          = Z3
    , proverCmd           = "z3"
    , proverArgs          = \_ _ -> words "-tptp -nw /dev/stdin"
    , proverShort         = 'z'
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
    , proverArgs          = \_ t -> words ("--proof tptp --mode casc -t " ++ show t)
    , proverShort         = 'v'
    }

spass :: Prover
spass = template
    { proverName          = SPASS
    , proverCmd           = "SPASS"
    , proverArgs          = \_ t -> words ("-Stdin -Auto -TPTP -PGiven=0 -PProblem=0 -DocProof=0 -PStatistic=0 -TimeLimit=" ++ show t)
    , proverProcessOutput = searchOutput
                                [("Proof found.",mkSuccess)
                                ,("Completion found.",const Failure)
                                ,("Ran out of time.",const Failure)]
    , proverShort         = 's'
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
eproofLemmaParser :: String -> [String]
eproofLemmaParser = mapMaybe parseLemma . lines

parseLemma :: String -> Maybe String
parseLemma s = case splitOn "Lemma{" s of
    [_,l] -> Just (takeWhile (/= '}') l)
    _     -> Nothing
