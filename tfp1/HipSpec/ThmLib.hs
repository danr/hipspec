{-# LANGUAGE RecordWildCards,DeriveFunctor #-}
module HipSpec.ThmLib where

import HipSpec.Property
import HipSpec.Theory
import HipSpec.ATP.Provers

import Control.Concurrent.STM.Promise.Tree
import Data.List(intercalate)

{-# ANN module "HLint: ignore Use camelCase" #-}

-- One subtheory with a conjecture with all dependencies
type ProofObligation = Obligation Subtheory
type ProofTree       = Tree ProofObligation

data Theorem eq = Theorem
    { thm_prop    :: Property
    , thm_proof   :: Proof
    , thm_lemmas  :: Maybe [Property]
    , thm_provers :: [ProverName]
    }
  deriving Show

data Proof = ByInduction { ind_vars :: [String] }
  deriving Show

definitionalTheorem :: Theorem eq -> Bool
definitionalTheorem Theorem{..} = case thm_proof of
    ByInduction{..} -> null ind_vars

data Obligation a = Obligation
    { ob_prop     :: Property
    , ob_info     :: ObInfo
    , ob_content  :: a
    -- ^ This will be a theory, TPTP string or prover results
    }
  deriving (Show,Functor)

data ObInfo
    = Induction
        { ind_coords :: [Int]
        , ind_num    :: Int
        , ind_nums   :: Int
        }
  deriving Show

obInfoFileName :: ObInfo -> String
obInfoFileName (Induction cs n _)
    = intercalate "_" (map show cs) ++ "__" ++ show n
