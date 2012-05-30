module Halt.Conf where

-- Translation configuration

data HaltConf = HaltConf
    { use_min     :: Bool
    -- ^ Use min translation
    , use_cf      :: Bool
    -- ^ Translate CF
    , unr_and_bad :: Bool
    -- ^ Use UNR and BAD when translating
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaltConf -> HaltConf
sanitizeConf = id
