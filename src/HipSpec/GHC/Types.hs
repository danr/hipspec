module HipSpec.GHC.Types
    ( EntryResult(..)
    , SigInfo(..)
    , SigMap(..)
    , SigGlue(..)
    ) where

import Test.QuickSpec.Term
import Test.QuickSpec.Signature

import GHC hiding (Sig)
import Var
import CoreSyn

import Data.Map (Map)
import qualified Data.Typeable as Typeable

-- | The result from calling GHC
data EntryResult = EntryResult
    { sig_info   :: Maybe SigInfo
    , core_props :: [(Var,CoreExpr)]
    }

-- | Signature from QuickSpec
data SigInfo = SigInfo
    { sig     :: Sig
    , sig_map :: SigMap
    }

-- | Mappings for QuickSpec symbols and Typeable Tycons to GHC Core structures
data SigMap = SigMap
    { sym_map   :: Map Symbol Id
    , tycon_map :: Map Typeable.TyCon TyCon
    }

-- | Used to make a SigMap from the names in scope from a signature
data SigGlue = SigGlue
    { signature_names  :: Map Symbol [Name]
    , signature_tycons :: Map Typeable.TyCon [Name]
    }

