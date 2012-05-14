{-# LANGUAGE RecordWildCards #-}
module Halt.ExprTrans where

import CoreSyn
import FastString
import Id
import Literal
import Unique

import FOL.Abstract hiding (App)

import Halt.Common
import Halt.Monad
import Halt.Utils
import Halt.Names

import qualified Data.Map as M
import Data.List (intercalate)

import Control.Monad.Reader

-- | Translate expressions, i.e. not case (nor let/lambda)
trExpr :: CoreExpr -> HaltM (Term Var)
trExpr e = do
    HaltEnv{..} <- ask
    let isFunction x = case M.lookup (idName x) arities of
                          Just i  -> i > 0
                          Nothing -> False
    case e of
        Var x | x `elem` quant -> return (qvar x)
              | isFunction x   -> return (ptr x)
              | otherwise      -> return (con x)
        App{} -> do
          write $ "App on " ++ showExpr e
          case second trimTyArgs (collectArgs e) of
            (Var f,es)
               | Just i <- M.lookup (idName f) arities -> do
                   write $ idToStr f ++ " has arity " ++ show i
                   if i > length es
                       then apps (ptr f) <$> mapM trExpr es
                       else do
                           let (es_inner,es_after) = splitAt i es
                           inner <- Fun f <$> mapM trExpr es_inner
                           apps inner <$> mapM trExpr es_after
            (f,es) -> do
               write $ "Collected to " ++ showExpr f
                           ++ concat [ "(" ++ show (getUnique (idName x)) ++ ") " | let Var x = f ]
                           ++ " on " ++ intercalate "," (map showExpr es)
               apps <$> trExpr f <*> mapM trExpr es
        Lit (MachStr s) -> do
          write $ "String, " ++ unpackFS s ++ " coerced to bad"
          return $ con (constantId BAD)
        Cast e' _ -> do
          write $ "Ignoring cast: " ++ showExpr e
          trExpr e'
        Case{}     -> trErr "case" -- trCaseExpr e
        Let{}      -> trErr "let"  -- trLet bind e'
        Lit{}      -> trErr "literals"
        Type{}     -> trErr "types"
        Lam{}      -> trErr "lambdas"
        Coercion{} -> trErr "coercions"
        Tick{}     -> trErr "ticks"
  where trErr s = error ("trExpr: no support for " ++ s ++ "\n" ++ showExpr e)
