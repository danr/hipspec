{-# LANGUAGE CPP #-}
module HipSpec.Sig.Scope where

import GHC hiding (Sig)

import Control.Applicative
import Data.Maybe

import DataCon

#if __GLASGOW_HASKELL__ >= 708
import ConLike
#endif

getIdsInScope :: (Id -> Id) -> Ghc [Id]
getIdsInScope fix_id = do

    ns <- getNamesInScope

    things <- catMaybes <$> mapM lookupName ns

    return [ fix_id i | AnId i <- things ]

parseName' :: String -> Ghc [Name]
parseName' = handleSourceError (\ _ -> return []) . parseName

inScope :: String -> Ghc Bool
inScope s = do
    xs <- parseName' s
    return $ if null xs then False else True

lookupString :: String -> Ghc [TyThing]
lookupString s = do
    xs <- parseName' s
    catMaybes <$> mapM lookupName xs

thingToId :: TyThing -> Maybe Id
thingToId (AnId i)     = Just i
#if __GLASGOW_HASKELL__ >= 708
thingToId (AConLike (RealDataCon dc)) = Just (dataConWorkId dc)
thingToId (AConLike (PatSynCon _pc))  = error "HipSpec.Sig.Scope: Pattern synonyms not supported"
#else
thingToId (ADataCon dc) = Just (dataConWorkId dc)
#endif
thingToId _            = Nothing

mapJust :: (a -> Maybe b) -> [a] -> Maybe b
mapJust k = listToMaybe . mapMaybe k

