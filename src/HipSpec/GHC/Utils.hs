{-# LANGUAGE CPP,PatternGuards #-}
module HipSpec.GHC.Utils where

import Outputable

import Var (Var,varName)
import Name (Name,getOccString)
import DataCon
import Id
import TyCon
import Type

#if __GLASGOW_HASKELL__ >= 708
import DynFlags (unsafeGlobalDynFlags)
#elif __GLASGOW_HASKELL__ >= 706
import DynFlags (tracingDynFlags)
#endif

portableShowSDoc :: SDoc -> String
#if __GLASGOW_HASKELL__ >= 708
portableShowSDoc = showSDoc unsafeGlobalDynFlags
#elif __GLASGOW_HASKELL__ >= 708
portableShowSDoc = showSDoc tracingDynFlags
#else
portableShowSDoc = showSDoc
#endif

-- | Shows something outputable
showOutputable :: Outputable a => a -> String
showOutputable = portableShowSDoc . ppr

varToString :: Var -> String
varToString = nameToString . varName

nameToString :: Name -> String
nameToString = getOccString

-- | Is this Id a "constructor" to a newtype?
--   This is the only way I have found to do it...
isNewtypeConId :: Id -> Bool
isNewtypeConId i
    | Just dc <- isDataConId_maybe i = isNewTyCon (dataConTyCon dc)
    | otherwise = False

-- | Is this Id a data or newtype constructor?
--
--   Note: cannot run isDataConWorkId on things that aren't isId,
--         then we get a panic from idDetails.
--
--         (mainly from type variables)
isDataConId :: Id -> Bool
isDataConId v = isId v && (isConLikeId v || isNewtypeConId v)

-- Removes class constraints
rmClass :: Type -> Type
rmClass ty = case splitFunTy_maybe ty of
    Just (t1,t2) | isPredTy t1 -> rmClass t2
    _ -> ty

