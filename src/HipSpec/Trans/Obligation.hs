{-# LANGUAGE DeriveFunctor,DeriveGeneric #-}
module HipSpec.Trans.Obligation where

import HipSpec.Trans.Property
import GHC.Generics
import Data.Aeson

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
  deriving (Eq, Ord, Show, Generic)

instance ToJSON ObInfo

