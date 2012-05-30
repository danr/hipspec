module Hip.Provers where

import Hip.ResultDatatypes
import Data.List

data ProverName = E | Vampire | Vampire64 | Prover9 | SPASS | Equinox | Z3
  deriving (Eq,Ord)

instance Show ProverName where
  show Z3        = "z3"
  show E         = "eprover"
  show Vampire   = "vampire"
  show Vampire64 = "vampire (64)"
  show Prover9   = "prover9"
  show SPASS     = "spass"
  show Equinox   = "equinox"

data Prover = Prover { proverName          :: ProverName
                     -- ^ Name of the prover in the prover datatype
                     , proverCmd           :: String
                     -- ^ system command to createProcess
                     , proverArgs          :: Int -> [String]
                     -- ^ given timeout in secs, args to createProcess
                     , proverProcessOutput :: String -> Integer -> ProverResult
                     -- ^ processes the output and time and gives a result
                     , proverShort         :: Char
                     -- ^ short char for command line options
                     }


-- Should really use something more efficient than isInfixOf
searchOutput :: [(String,time -> ProverResult)] -> String -> time -> ProverResult
searchOutput []         output _ = Unknown output
searchOutput ((s,r):xs) output time
    | s `isInfixOf` output = r time
    | otherwise            = searchOutput xs output time


statusSZS :: [(String,Integer -> ProverResult)]
statusSZS = [("Theorem",Success),("Unsatisfiable",Success)
            ,("CounterSatisfiable",const Failure),("Timeout",const Failure)]

allProvers :: [Prover]
allProvers = [vampire,vampire64,prover9,spass,eprover,equinox,z3]

proversFromString :: String -> [Prover]
proversFromString str = filter ((`elem` str) . proverShort) allProvers

eprover :: Prover
eprover = Prover
  { proverName          = E
  , proverCmd           = "eprover"
  , proverArgs          = \_ -> words "-tAuto -xAuto --tptp3-format -s"
  , proverProcessOutput = searchOutput statusSZS
  , proverShort         = 'e'
  }

z3 :: Prover
z3 = Prover
  { proverName          = Z3
  , proverCmd           = "z3"
  , proverArgs          = \_ -> words "-tptp -nw /dev/stdin"
  , proverProcessOutput = searchOutput statusSZS
  , proverShort         = 'z'
  }

vampire :: Prover
vampire = Prover
  { proverName          = Vampire
  , proverCmd           = "vampire_lin32"
  , proverArgs          = \t -> words ("--proof tptp --mode casc -t " ++ show t)
  , proverProcessOutput = searchOutput statusSZS
  , proverShort         = 'v'
  }

vampire64 :: Prover
vampire64 = vampire
  { proverName          = Vampire64
  , proverCmd           = "vampire_lin64"
  , proverShort         = 'V'
  }

prover9 :: Prover
prover9 = Prover
  { proverName          = Prover9
  , proverCmd           = "prover9script"
  , proverArgs          = \t -> [show t]
  , proverProcessOutput = searchOutput [("THEOREM PROVED",Success),("SEARCH FAILED",const Failure)]
  , proverShort         = 'p'
  }

spass :: Prover
spass = Prover
  { proverName          = SPASS
  , proverCmd           = "SPASS"
  , proverArgs          = \t -> words ("-Stdin -Auto -TPTP -PGiven=0 -PProblem=0 -DocProof=0 -PStatistic=0 -TimeLimit=" ++ show t)
  , proverProcessOutput = searchOutput [("Proof found.",Success),("Completion found.",const Failure),("Ran out of time.",const Failure)]
  , proverShort         = 's'
  }

equinox :: Prover
equinox = Prover
  { proverName          = Equinox
  , proverCmd           = "equinox"
  , proverArgs          = \_ -> words ("--tstp --split /dev/stdin")
  , proverProcessOutput = searchOutput statusSZS
  , proverShort         = 'x'
  }