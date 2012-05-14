module Halt.Conf where

-- Translation configuration

data HaltConf = HaltConf
    { use_cnf      :: Bool
    -- ^ Output many formulas in cnf instead
    , inline_projs :: Bool
    -- ^ Write plus(succ(x),y) instead of x=succ(pred(x)) => plus(succ(pred(x),y)
    , use_min      :: Bool
    -- ^ Use min translation
    , common_min   :: Bool
    -- ^ Write f(x) = k & min(k) => k = ... instead of min(f(x)) => f(x) = ...
    , unr_and_bad  :: Bool
    -- ^ Use UNR and BAD instead of bottom when translating
    }
  deriving (Eq,Ord,Show)

sanitizeConf :: HaltConf -> HaltConf
sanitizeConf hc = hc { common_min = common_min hc && use_min hc }
