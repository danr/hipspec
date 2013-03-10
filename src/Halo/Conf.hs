{-

    Translation configuration

-}
module Halo.Conf where

data HaloConf = HaloConf
    { use_bottom :: Bool
    -- ^ Generate a theory with bottoms
    , var_scrut_constr   :: Bool
    -- ^ Make a constraint instead of inline casing on variables
    }
  deriving (Eq,Ord,Show)

