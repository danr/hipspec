module Halo.Conf where

-- Translation configuration

data HaloConf = HaloConf
    { use_min     :: Bool
    -- ^ Use min translation
    , use_minrec  :: Bool
    -- ^ Use minrec translation (hipspec)
    , use_cf      :: Bool
    -- ^ Translate CF
    , unr_and_bad :: Bool
    -- ^ Use UNR and BAD when translating
    , ext_eq      :: Bool
    -- ^ Make function pointer axioms depend on extensional equality
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaloConf -> HaloConf
sanitizeConf = id
