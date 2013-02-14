{-# LANGUAGE DeriveFunctor #-}
module HipSpec.Trans.Obligation where

import Data.Function
import Data.List

import Var

import HipSpec.Trans.Theory (HipSpecContent,HipSpecSubtheory)

import Halo.Subtheory
import Halo.FOL.Abstract

import HipSpec.Trans.Property

data Obligation a = Obligation
    { ob_property :: Property
    , ob_content  :: a
    }
  deriving (Functor,Show)

data Proof a = Induction
    { ind_coords  :: [Int]
    , ind_num     :: Int
    , ind_nums    :: Int
    , ind_content :: a
    -- ^ This will be a theory, TPTP string or prover results
    }
  deriving (Functor)

