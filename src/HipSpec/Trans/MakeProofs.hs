{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.MakeProofs (makeProofs) where

import Data.List (nub)

import HipSpec.Trans.MakerMonad
import HipSpec.Trans.Induction
import HipSpec.Trans.Obligation
import HipSpec.Trans.Property as Prop
import HipSpec.Params

import Control.Concurrent.STM.Promise.Tree

import Halo.Monad
import Halo.Util

import Data.Maybe (mapMaybe)

import Control.Monad.Reader
import Control.Monad.Error

makeProofs :: forall eq . Params -> Property eq -> MakerM (ProofTree eq)
makeProofs params@Params{methods,indvars,inddepth} prop@Property{propVars}
    = requireAny <$>
        (sequence (mapMaybe (induction params prop) induction_coords) `catchError` \ _ -> do
          lift $ cleanUpFailedCapture
          return [])
  where
    induction_coords :: [[Int]]
    induction_coords = nub $
        [ concat (replicate depth var_ixs)
        -- For each variable, repeat it to the depth
        | var_ixs <- var_pow
        -- Consider all sets of variables
        , length var_ixs <= indvars
        , 'p' `elem` methods || length var_ixs > 0
        -- Don't do induction on too many variables
        , depth <- [start_depth..stop_depth]
        ]
      where
        var_indicies :: [Int]
        var_indicies = zipWith const [0..] propVars

        var_pow :: [[Int]]
        var_pow = filterM (const [False,True]) var_indicies

        start_depth | 'p' `elem` methods = 0
                    | otherwise          = 1
        stop_depth  | 'i' `elem` methods = inddepth
                    | otherwise          = 0

