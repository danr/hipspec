module Halo.Conf where

-- Translation configuration

data HaloConf = HaloConf
    { use_min           :: Bool
    -- ^ Use min translation
    , use_minrec  :: Bool
    -- ^ Use minrec translation
    , unr_and_bad       :: Bool
    -- ^ Use UNR and BAD when translating
    , ext_eq            :: Bool
    -- ^ Make function pointer axioms depend on extensional equality
    , disjoint_booleans :: Bool
    -- ^ Always add true /= false even though they might not be min
    , or_discr          :: Bool
    -- ^ Use or instead of and in the assumptions of discrimination axioms
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaloConf -> HaloConf
sanitizeConf = id
