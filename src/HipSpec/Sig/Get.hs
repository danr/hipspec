module HipSpec.Sig.Get (getSignature) where

import QuickSpec.Signature
import HipSpec.Sig.Scope

import GHC

import Data.Dynamic

getSignature :: Ghc (Maybe Signature)
getSignature = do
    ok <- inScope "sig"
    if ok
        then mapJust fromDynamic `fmap` mapM dynCompileExpr [ "sig" ]
        else return Nothing

