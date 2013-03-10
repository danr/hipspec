{-# LANGUAGE RecordWildCards #-}
{-

    Adds alternatives to UNR and BAD in cases.

    No DEFAULT branch. Add such a case to UNR, and one BAD -> BAD:

        case e of                  case e of
          K1 a    -> e1              DEFAULT -> UNR
          K2 a b  -> e2      =>      K1 a    -> e1
                                     K2 a b  -> e2
                                     BAD     -> BAD

    Use RemoveDefaults to remove the default branches

-}
module Halo.Case (addBottomCase,mkLefts,rmLefts) where

import CoreSyn
import CoreUtils
import Type

import Halo.Monad
import Halo.Conf
import Halo.MonoType

import Halo.FOL.Abstract

import Control.Monad.Error
import Control.Monad.Reader

mkLefts :: [(a,b,c)] -> [(a,b,Either c d)]
mkLefts = map (\ (a,b,c) -> (a,b,Left c))

rmLefts :: [(a,b,Either c d)] -> [(a,b,c)]
rmLefts = map (\ (a,b,Left c) -> (a,b,c))

-- | Adds alts to BAD and UNR as described above
addBottomCase :: Type -> [CoreAlt] -> HaloM [(AltCon,[Var],Either CoreExpr Term')]
addBottomCase ty alts = do
    HaloConf{..} <- asks conf
    if not use_bottom then return (mkLefts alts) else
        case findDefault alts of
            (_as,Just _def) -> throwError "Default branch found though use_bottom"
            (as,Nothing) -> do
                monoty <- monoType ty
                return $ (DEFAULT, [], Right (bottom monoty)):mkLefts as

