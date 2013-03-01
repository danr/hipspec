{-# LANGUAGE DeriveFunctor,DeriveGeneric #-}
module HipSpec.Trans.Obligation where

import HipSpec.Trans.Property
import GHC.Generics
import Data.Aeson

data Obligation eq a = Obligation
    { ob_property :: Property eq
    , ob_content  :: a
    }
  deriving (Functor,Show)

data Proof a = Induction
    { ind_coords    :: [Int]
    , ind_num       :: Int
    , ind_nums      :: Int
    , proof_content :: a
    -- ^ This will be a theory, TPTP string or prover results
    }
  deriving (Functor,Show)

data SimpleProof = SInduction
    { sind_coords :: [Int]
    , sind_num    :: Int
    , sind_nums   :: Int
    }
  deriving (Eq, Ord, Show, Generic)

instance ToJSON SimpleProof

toSimple :: Proof a -> SimpleProof
toSimple (Induction a b c _) = SInduction a b c

