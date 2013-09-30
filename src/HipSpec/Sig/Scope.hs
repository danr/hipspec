module HipSpec.Sig.Scope where

import GHC hiding (Sig)

import Control.Applicative
import Data.Maybe

import DataCon

getIdsInScope :: Ghc [Id]
getIdsInScope = do

    ns <- getNamesInScope

    things <- catMaybes <$> mapM lookupName ns

    return [ i | AnId i <- things ]

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
thingToId (ADataCon i) = Just (dataConWorkId i)
thingToId _            = Nothing

mapJust :: (a -> Maybe b) -> [a] -> Maybe b
mapJust k = listToMaybe . mapMaybe k

