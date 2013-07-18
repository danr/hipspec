{-# LANGUAGE NamedFieldPuns,TypeOperators,ScopedTypeVariables,RecordWildCards #-}
module HipSpec.MakeProofs (makeProofs) where

import Data.List (nub)

import HipSpec.ThmLib
import HipSpec.Induction
import HipSpec.Property as Prop
import HipSpec.Params

import HipSpec.Monad

import Data.Maybe (mapMaybe)
import Control.Monad (filterM)

makeProofs :: forall eq . Property eq -> HS [[ProofObligation eq]]
makeProofs prop@Property{prop_vars} = do

    params@Params{techniques,indvars,inddepth} <- getParams

    Env{..} <- getEnv

    let induction_coords :: [[Int]]
        induction_coords = nub
            [ concat (replicate depth var_ixs)
            -- For each variable, repeat it to the depth
            | var_ixs <- var_pow
            -- Consider all sets of variables
            , length var_ixs <= indvars
            , Plain `elem` techniques || not (null var_ixs)
            -- Don't do induction on too many variables
            , depth <- [start_depth..stop_depth]
            ]
          where
            var_indicies :: [Int]
            var_indicies = zipWith const [0..] prop_vars

            var_pow :: [[Int]]
            var_pow = filterM (const [False,True]) var_indicies

            start_depth | Plain `elem` techniques       = 0
                        | otherwise                     = 1
            stop_depth  | Induction `elem` techniques = inddepth
                        | otherwise                     = 0

        attempts = mapMaybe (induction params ty_env arity_map prop) induction_coords

    return attempts

