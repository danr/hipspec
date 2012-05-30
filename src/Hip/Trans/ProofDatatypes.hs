{-# LANGUAGE DeriveFunctor #-}
module Hip.Trans.ProofDatatypes where

import Data.Function

import Halt.FOL.Abstract

data ProofMethod
    = Plain
    | StructuralInduction { indVars :: [String]
                          , depth :: Int }
  deriving (Eq,Ord)

instance Show ProofMethod where
    show Plain                      = "plain"
    show (StructuralInduction vs d) = "structural induction on "
                                    ++ unwords vs ++ " depth " ++ show d

proofMethodFile :: ProofMethod -> String
proofMethodFile pt = case pt of
    Plain                    -> "plain"
    StructuralInduction vs d -> concat vs ++ show d

type Property  = PropertyMatter [Part]
type Part      = PartMatter     ([AxClause],[VarClause],[Particle])
type Particle  = ParticleMatter [VarClause]

data PropertyMatter m = Property { propName   :: String
                                 -- ^ The identifier of the property
                                 , propCode   :: String
                                 -- ^ Some representiation
                                 , propMatter :: m
                                 -- ^ The meat of the property
                                 }
  deriving (Show,Functor)

instance Eq (PropertyMatter m) where
  (==) = (==) `on` propName

instance Ord (PropertyMatter m) where
  compare = compare `on` propName

data PartMatter m = Part { partMethod    :: ProofMethod
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

extendPart :: [VarClause] -> Part -> Part
extendPart vc' (Part n (ac,vc,p)) = Part n (ac,vc++vc',p)
