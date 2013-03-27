module HipSpec.GHC.GetSig (getSignature) where

import Test.QuickSpec.Signature

import GHC hiding (Sig)
import OccName hiding (varName)
import Name hiding (varName)

import Data.Dynamic

import Data.Maybe

getSignature :: [Name] -> Ghc (Maybe Sig)
getSignature scope
    | any (\ n -> occNameString (nameOccName n) == "sig") scope
        = mapJust fromDynamic `fmap` mapM dynCompileExpr
            [ "sig"
            , "Test.QuickSpec.Signature.signature sig"
            ]
    | otherwise = return Nothing

mapJust :: (a -> Maybe b) -> [a] -> Maybe b
mapJust k = listToMaybe . mapMaybe k

