module Halo.Conf where

-- Translation configuration

data HaloConf = HaloConf
    { use_min     :: Bool
    -- ^ Use min translation
    , use_cf      :: Bool
    -- ^ Translate CF
    , unr_and_bad :: Bool
    -- ^ Use UNR and BAD when translating
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaloConf -> HaloConf
sanitizeConf = id
