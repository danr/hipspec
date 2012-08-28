{-

    Translation configuration

-}
module Halo.Conf where

data HaloConf = HaloConf
    { use_min           :: Bool
    -- ^ Use min translation
    , use_minrec        :: Bool
    -- ^ Use minrec translation
    , unr_and_bad       :: Bool
    -- ^ Use UNR and BAD when translating
    , ext_eq            :: Bool
    -- ^ Make function pointer axioms depend on extensional equality
    , or_discr          :: Bool
    -- ^ Use or instead of and in the assumptions of discrimination axioms
    , var_scrut_constr  :: Bool
    -- ^ Make a constraint instead of inline casing on variables
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaloConf -> HaloConf
sanitizeConf = id
