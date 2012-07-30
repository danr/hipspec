{-# LANGUAGE RecordWildCards, PatternGuards #-}
module Halo.ExprTrans where

import CoreSyn
import FastString
import Literal
import MkCore

import Halo.FOL.Abstract
import Halo.Monad
import Halo.PrimCon
import Halo.Shared
import Halo.Util

import qualified Data.Map as M

import Control.Monad.Reader
import Control.Monad.Error

-- | Translate expressions, i.e. not case (nor let/lambda)
--
--   This function registers used function pointers as a side-effect.
--   To capture them, run `capturePtrs', see Halo.Monad
--
--   trExpr looks at the following entries of HaloEnv
--
--       * skolems
--       * arities
--
--   If a variable is not a skolem variable, and not in arities, it is
--   deemed as quantified.
trExpr :: CoreExpr -> HaloM Term'
trExpr e = do
    HaloEnv{..} <- ask
    let isPAP x = case M.lookup x arities of
                          Just i  -> i > 0
                          Nothing -> False
        isQuant x = x `M.notMember` arities
    case e of
        Var x
            | x `elem` errorIds -> return bad
            | x `elem` skolems  -> return (skolem x)
            | isPAP x           -> usePtr x >> return (ptr x)
            | isQuant x         -> return (qvar x)
            | otherwise         -> return (con x) -- con or caf
        App{} -> case second trimTyArgs (collectArgs e) of
            (Var f,es)
                 | null es -> trExpr (Var f)
                 | f `elem` errorIds -> return bad
                 | Just i <- M.lookup f arities -> do
                     if i > length es
                         then do usePtr f
                                 apps (ptr f) <$> mapM trExpr es
                         else do let (es_inner,es_after) = splitAt i es
                                 inner <- apply f <$> mapM trExpr es_inner
                                 apps inner <$> mapM trExpr es_after
            (f,es) -> apps <$> trExpr f <*> mapM trExpr es
        Lit (MachStr s) -> do
          write $ "String, " ++ unpackFS s ++ " coerced to bad"
          return bad
        Cast e' _ -> do
          write $ "Ignoring cast: " ++ showExpr e
          trExpr e'
        Case{}     -> intErr "case"
        Let{}      -> intErr "let"
        Lam{}      -> intErr "lambdas"
        Lit{}      -> trErr "literals"
        Type{}     -> trErr "types"
        Coercion{} -> trErr "coercions"
        Tick{}     -> trErr "ticks"
  where
    trErr s  = throwError $ "trExpr: no support for " ++ s
                         ++ "\n    in expression: " ++ showExpr e
    intErr s = throwError $ "trExpr: internal error, unexpected " ++ s
                         ++ "\n    in expression: " ++ showExpr e
