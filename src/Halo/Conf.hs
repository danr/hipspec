module Halo.Conf where

-- Translation configuration

data HaloConf = HaloConf
    { use_min           :: Bool
    -- ^ Use min translation
    , use_cf            :: Bool
    -- ^ Translate CF
    , unr_and_bad       :: Bool
    -- ^ Use UNR and BAD when translating
    , ext_eq            :: Bool
    -- ^ Make function pointer axioms depend on extensional equality
    , disjoint_booleans :: Bool
    -- ^ Always add true /= false even though they might not be min
    , or_discr          :: Bool
    -- ^ Use Or instead of And in the assumptions of discrimination axioms
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaloConf -> HaloConf
sanitizeConf = id
