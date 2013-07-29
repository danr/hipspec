module HipSpec.Sig.Get (getSignature) where

import Test.QuickSpec.Signature

import GHC hiding (Sig)

import HipSpec.GHC.Utils

import Data.Dynamic

import Data.Maybe

getSignature :: [Name] -> Ghc (Maybe Sig)
getSignature scope
    | any (\ n -> nameToString n == "sig") scope
        = mapJust fromDynamic `fmap` mapM dynCompileExpr
            [ "sig"
            , "Test.QuickSpec.Signature.signature sig"
            ]
    | otherwise = return Nothing

mapJust :: (a -> Maybe b) -> [a] -> Maybe b
mapJust k = listToMaybe . mapMaybe k

