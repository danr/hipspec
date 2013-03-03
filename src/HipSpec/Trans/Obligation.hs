{-# LANGUAGE DeriveFunctor, DeriveGeneric, RecordWildCards #-}
module HipSpec.Trans.Obligation where

import HipSpec.Trans.Property
import HipSpec.ATP.Provers
import GHC.Generics
import Data.Aeson

data Theorem eq = Theorem
    { thm_prop    :: Property eq
    , thm_proof   :: Proof
    , thm_lemmas  :: Maybe [Property eq]
    , thm_provers :: [ProverName]
    }
  deriving (Functor,Show)

data Proof = ByInduction { ind_vars :: [String] }
  deriving Show

definitionalTheorem :: Theorem eq -> Bool
definitionalTheorem Theorem{..} = case thm_proof of
    ByInduction{..} -> null ind_vars

data Obligation eq a = Obligation
    { ob_prop     :: Property eq
    , ob_info     :: ObInfo
    , ob_content  :: a
    -- ^ This will be a theory, TPTP string or prover results
    }
  deriving (Functor,Show)

data ObInfo = Induction
    { ind_coords :: [Int]
    , ind_num    :: Int
    , ind_nums   :: Int
    }
  deriving (Eq,Ord,Show,Generic)

instance ToJSON ObInfo

