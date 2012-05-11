{-# LANGUAGE RecordWildCards #-}
module Halt.ExprTrans where

import CoreSyn
import FastString
import Id
import Literal
import Unique

import FOL.Syn hiding ((:==))

import Halt.Common
import Halt.Monad
import Halt.Utils

import qualified Data.Map as M
import Data.List (intercalate)

import Control.Monad.Reader

-- | Translate expressions, i.e. not case (nor let/lambda)
trExpr :: CoreExpr -> HaltM Term
trExpr e = do
    HaltEnv{..} <- ask
    let isFunction x = case M.lookup (idName x) arities of
                          Just i  -> i > 0
                          Nothing -> False
    case e of
        Var x | x `elem` quant -> return (mkVar x)
              | isFunction x   -> return (mkPtr x)
              | otherwise      -> return (mkFun x [])
        App{} -> do
          write $ "App on " ++ showExpr e
          case second trimTyArgs (collectArgs e) of
            (Var x,es)
               | Just i <- M.lookup (idName x) arities -> do
                   write $ idToStr x ++ " has arity " ++ show i
                   if i > length es
                       then foldFunApps (mkPtr x) <$> mapM trExpr es
                       else do
                           let (es_inner,es_after) = splitAt i es
                           inner <- mkFun x <$> mapM trExpr es_inner
                           foldFunApps inner <$> mapM trExpr es_after
            (f,es) -> do
               write $ "Collected to " ++ showExpr f
                           ++ concat [ "(" ++ show (getUnique (idName x)) ++ ") " | let Var x = f ]
                           ++ " on " ++ intercalate "," (map showExpr es)
               foldFunApps <$> trExpr f <*> mapM trExpr es
        Lit (MachStr s) -> do
          write $ "String to constant: " ++ unpackFS s
          return $ Fun (FunName "string") [Fun (FunName (unpackFS s)) []]

        Case{}      -> trErr "case" -- trCaseExpr e
        Let{}       -> trErr "let"  -- trLet bind e'
        Cast e' _   -> do
          write $ "Ignoring cast: " ++ showExpr e
          trExpr e'

        Lit{}      -> trErr "literals"
        Type{}     -> trErr "types"
        Lam{}      -> trErr "lambdas"
        Coercion{} -> trErr "coercions"
        Tick{}     -> trErr "ticks"
  where trErr s = error ("trExpr: no support for " ++ s ++ "\n" ++ showExpr e)
