{-# LANGUAGE DeriveFunctor,NamedFieldPuns #-}
module Hip.Trans.ProofDatatypes where

import qualified Language.TPTP as T
import Hip.Trans.Core
import Data.Function

proofDatatypes :: [Name]
proofDatatypes = ["Prop"]

proveFunctions :: [Name]
proveFunctions = ["prove","proveBool","given","givenBool","=:="]

provable :: Expr -> Bool
provable (App f es) = f `elem` proveFunctions || any provable es
provable _          = False

data ProofMethod = Plain
                 | SimpleInduction         { indVar :: Name }
                 | ApproxLemma
                 | FixpointInduction       { fixFuns :: [Name] }
                 | StructuralInduction     { indVars :: [Name]
                                           , addBottom :: Bool
                                           , depth :: Int }
  deriving (Eq,Ord)

data Coverage = Infinite
              -- ^ Infinite and partial values
              | Finite
              -- ^ Finite and total values
  deriving (Eq,Ord,Show)

instance Show ProofMethod where
  show Plain                       = "plain"
  show (SimpleInduction v)         = "simple induction on " ++ v
  show ApproxLemma                 = "approximation lemma"
  show (FixpointInduction f)       = "fixed point induction on " ++ unwords f
  show (StructuralInduction vs b d) = concat [ "finite " | not b ] ++ "structural induction on " ++
                                      unwords vs ++ " depth " ++ show d

proofMethodFile :: ProofMethod -> String
proofMethodFile pt = case pt of
  Plain                      -> "plain"
  SimpleInduction v          -> "simpleind" ++ v
  ApproxLemma                -> "approx"
  FixpointInduction f        -> "fix" ++ concat f
  StructuralInduction vs b d -> concat vs ++ show d


proofMethods :: [ProofMethod]
proofMethods = [Plain
               ,StructuralInduction [] True 0
               ,ApproxLemma
               ,FixpointInduction []
               ,StructuralInduction [] False 0
               ]


liberalEq :: ProofMethod -> ProofMethod -> Bool
liberalEq Plain                        Plain                       = True
liberalEq SimpleInduction{}            SimpleInduction{}           = True
liberalEq ApproxLemma                  ApproxLemma                 = True
liberalEq FixpointInduction{}          FixpointInduction{}         = True
liberalEq (StructuralInduction _ b' _) (StructuralInduction _ b _) = b == b'
liberalEq _ _                                                      = False

liberalShow :: ProofMethod -> String
liberalShow Plain                     = "plain"
liberalShow SimpleInduction{}         = "simple induction"
liberalShow ApproxLemma               = "approximation lemma"
liberalShow FixpointInduction{}       = "fixed point induction"
liberalShow StructuralInduction{}     = "structural induction"

latexShow :: ProofMethod -> String
latexShow Plain                     = "plain"
latexShow SimpleInduction{}         = "simple ind"
latexShow ApproxLemma               = "approx"
latexShow FixpointInduction{}       = "fixpoint ind"
latexShow StructuralInduction{}     = "struct ind"

type Property  = PropertyMatter [Part]
type Part      = PartMatter     ([T.Decl],[Particle])
type Particle  = ParticleMatter [T.Decl]

data PropertyMatter m = Property { propName   :: Name
                                 , propCode   :: String
                                 , propMatter :: m
                                 }
  deriving (Show,Functor)

instance Eq (PropertyMatter m) where
  (==) = (==) `on` propName

instance Ord (PropertyMatter m) where
  compare = compare `on` propName


data PartMatter m = Part { partMethod    :: ProofMethod
                         , partCoverage  :: Coverage
                         , partMatter    :: m
                         }
  deriving (Show,Functor)

instance Eq (PartMatter m) where
  (==) = (==) `on` partMethod

instance Ord (PartMatter m) where
  compare = compare `on` partMethod

data ParticleMatter m = Particle { particleDesc   :: String
                                 , particleMatter :: m
                                 }
  deriving (Eq,Ord,Show,Functor)

extendParticle :: [T.Decl] -> Particle -> Particle
extendParticle axioms p = p { particleMatter = particleMatter p ++ axioms }

extendPart :: [T.Decl] -> Part -> Part
extendPart axioms (Part n c (theory,ps)) = Part n c (axioms ++ theory,ps)
