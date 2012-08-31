{-# LANGUAGE RecordWildCards, PatternGuards #-}
{-

    Translate expressions, i.e. not case (nor let/lambda)

    This function registers used function pointers as a side-effect.
    To capture them, run `capturePtrs', see Halo.Monad

    TODO: register if app was used

    trExpr looks at the following entries of HaloEnv

        * skolems
        * arities

    If a variable is not a skolem variable, and not in arities, it is
    deemed as quantified.

-}
module Halo.ExprTrans where

import CoreSyn
import CoreUtils
import Literal
import Name hiding (varName)
import Module
import Var

import Halo.FOL.Abstract
import Halo.Monad
import Halo.PrimCon
import Halo.Shared
import Halo.Util

import qualified Data.Map as M

import Control.Monad.Reader
import Control.Monad.Error

-- | Translate an expression to a term
trExpr :: CoreExpr -> HaloM Term'
trExpr e = do
    HaloEnv{..} <- ask
    let isPAP x = case M.lookup x arities of
                          Just i  -> i > 0
                          Nothing -> False
        isQuant x = x `M.notMember` arities
    case e of
        _ | exprIsBottom e -> return bad
        Var x
            | x `elem` skolems  -> return (skolem x)
            | isPAP x           -> usePtr x >> return (ptr x)
            | isQuant x         -> return (qvar x)
            | otherwise         -> return (con x) -- con or caf
        App{} -> case second trimTyArgs (collectArgs e) of
            (Var f,es)
                | null es -> trExpr (Var f)
                | Just i <- M.lookup f arities -> do
                    if i > length es
                        then do
                            usePtr f
                            regApp
                            apps (ptr f) <$> mapM trExpr es
                        else do
                            let (es_inner,es_after) = splitAt i es
                            unless (null es_after) regApp
                            inner <- apply f <$> mapM trExpr es_inner
                            apps inner <$> mapM trExpr es_after
                | Just p <- trPrim f (length es) ->
                    p <$> mapM trExpr es
            (f,es) -> do
                unless (null es) regApp
                apps <$> trExpr f <*> mapM trExpr es
{-
        Lit (MachStr s) -> do
            write $ "String, " ++ unpackFS s ++ " coerced to bad"
            return bad
-}
        Cast e' _ -> do
            write $ "Ignoring cast: " ++ showExpr e ++
                    "(hoping that it is a newtype cast)"
            trExpr e'
        -- Int
        Lit (MachInt i)      -> return (litInteger i)
        -- Integer
        Lit (LitInteger i _) -> return (litInteger i)
        Lit{}      -> trErr "non-integer literals"
        Type{}     -> trErr "types"
        Coercion{} -> trErr "coercions"
        Tick{}     -> trErr "ticks"
        Case{}     -> intErr "case"
        Let{}      -> intErr "let"
        Lam{}      -> intErr "lambdas"
  where
    trErr s  = throwError $ "trExpr: no support for " ++ s
                         ++ "\n    in expression: " ++ showExpr e
    intErr s = throwError $ "trExpr: internal error, unexpected " ++ s
                         ++ "\n    in expression: " ++ showExpr e

trPrim :: Var -> Int -> Maybe ([Term'] -> Term')
trPrim v no_args = do
    let n = getOccString v
    m <- moduleNameString . moduleName <$> nameModule_maybe (varName v)
    M.lookup (m,n,no_args) prims
  where
    liftBool t = prim LiftBool [t]
    prims = M.fromList
        [(("GHC.Prim","+#" ,2),prim Add)
        ,(("GHC.Prim","-#" ,2),prim Sub)
        ,(("GHC.Prim","*#" ,2),prim Mul)
        ,(("GHC.Prim","==#",2),liftBool . prim Eq)
        ,(("GHC.Prim","/=#",2),liftBool . prim Ne)
        ,(("GHC.Prim","<#" ,2),liftBool . prim Lt)
        ,(("GHC.Prim","<=#",2),liftBool . prim Le)
        ,(("GHC.Prim",">=#",2),liftBool . prim Ge)
        ,(("GHC.Prim",">#" ,2),liftBool . prim Gt)
        ]
