{-# LANGUAGE RecordWildCards, PatternGuards #-}
module Halo.ExprTrans where

import CoreSyn
import FastString
import Id
import Literal
import MkCore

import Halo.FOL.Abstract
import Halo.Util
import Halo.Monad
import Halo.PrimCon

import Halo.Shared

import qualified Data.Map as M
import Data.List (intercalate)

import Control.Monad.Reader
import Control.Monad.Error

-- | Translate expressions, i.e. not case (nor let/lambda)
--
--   This function registers used function pointers as a side-effect.
--   To capture them, run `capturePtrs', see Halo.Monad
trExpr :: CoreExpr -> HaloM Term'
trExpr e = do
    HaloEnv{..} <- ask
    let isFunction x = case M.lookup (idName x) arities of
                          Just i  -> i > 0
                          Nothing -> False
    case e of
        Var x | x `elem` errorIds -> return (constant BAD)
              | x `elem` quant    -> return (qvar x)
              | isFunction x      -> usePtr x >> return (ptr x)
              | otherwise         -> return (con x)
        App{} -> do
          write $ "App on " ++ showExpr e
          case second trimTyArgs (collectArgs e) of
            (Var f,es)
               | null es -> trExpr (Var f)
               | f `elem` errorIds -> return (constant BAD)
               | Just i <- M.lookup (idName f) arities -> do
                   write $ idToStr f ++ " has arity " ++ show i
                   if i > length es
                       then do usePtr f
                               apps (ptr f) <$> mapM trExpr es
                       else do let (es_inner,es_after) = splitAt i es
                               inner <- apply f <$> mapM trExpr es_inner
                               apps inner <$> mapM trExpr es_after
            (f,es) -> do
                 write $ "Collected to " ++ showExpr f
                             ++ " on " ++ intercalate "," (map showExpr es)
                 apps <$> trExpr f <*> mapM trExpr es
        Lit (MachStr s) -> do
          write $ "String, " ++ unpackFS s ++ " coerced to bad"
          return $ constant BAD
        Cast e' _ -> do
          write $ "Ignoring cast: " ++ showExpr e
          trExpr e'
        Case{}     -> intErr "case"
        Let{}      -> intErr "let"
        Lit{}      -> trErr "literals"
        Type{}     -> trErr "types"
        Lam{}      -> trErr "lambdas"
        Coercion{} -> trErr "coercions"
        Tick{}     -> trErr "ticks"
  where
    trErr s  = throwError $ "trExpr: no support for " ++ s
                         ++ "\n    in expression: " ++ showExpr e
    intErr s = throwError $ "trExpr: internal error, unexpected " ++ s
                         ++ "\n    in expression: " ++ showExpr e
