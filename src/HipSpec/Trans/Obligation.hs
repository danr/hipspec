{-# LANGUAGE DeriveFunctor #-}
module HipSpec.Trans.Obligation where

import HipSpec.Trans.Property

data Obligation a = Obligation
    { ob_property :: Property
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

