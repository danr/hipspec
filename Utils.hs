{-# LANGUAGE CPP #-}
module Utils where

import Outputable

#if __GLASGOW_HASKELL__ >= 706
import DynFlags (tracingDynFlags)
#endif

portableShowSDoc :: SDoc -> String
#if __GLASGOW_HASKELL__ >= 706
portableShowSDoc = showSDoc tracingDynFlags
#else
portableShowSDoc = showSDoc
#endif

-- | Shows something outputable
showOutputable :: Outputable a => a -> String
showOutputable = portableShowSDoc . ppr

