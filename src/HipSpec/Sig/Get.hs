module HipSpec.Sig.Get (getSignature) where

import Test.QuickSpec.Signature
import HipSpec.Sig.Scope

import GHC hiding (Sig)

import Data.Dynamic

getSignature :: Ghc (Maybe Sig)
getSignature = do
    ok <- inScope "sig"
    if ok
        then mapJust fromDynamic `fmap` mapM dynCompileExpr
                [ "sig"
                , "Test.QuickSpec.Signature.signature sig"
                ]
        else return Nothing

