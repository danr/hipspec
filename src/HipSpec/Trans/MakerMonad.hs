{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.MakerMonad (runMakerM, MakerM, makeUnique) where

import Halo.Monad
import Control.Monad.State
import UniqSupply
import Unique

type MakerM = StateT UniqSupply HaloM

runMakerM :: HaloEnv -> UniqSupply -> MakerM a -> ((a,[String]),UniqSupply)
runMakerM env us mm
    = case runHaloMsafe env (runStateT mm us) of
        (Right ((hm,us')),msg) -> ((hm,msg),us')
        (Left err,_msg)
            -> error $ "Halo.Trans.MakeProofs.runMakerM, halo says: " ++ err

makeUnique :: MakerM Unique
makeUnique = do
    (u,us) <- takeUniqFromSupply `fmap` get
    put us
    return u

