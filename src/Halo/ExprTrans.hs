{-# LANGUAGE RecordWildCards, PatternGuards #-}
{-

    Translate expressions, i.e. not case (nor let/lambda)

    This function registers used function pointers as a side-effect.
    To capture them, run `capturePtrs', see Halo.Monad

    TODO: register if app was used

    trExpr looks at the following entries of HaloEnv

        * skolems
        * qvars


-}
module Halo.ExprTrans (trExpr',trExpr) where

import CoreSyn
import CoreUtils
import Literal
import Name hiding (varName)
import Module
import Var

import Halo.Deappify
import Halo.MonoType
import Halo.FOL.Abstract
import Halo.Monad
import Halo.Shared
import Halo.Util
import Halo.Conf

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Reader
import Control.Monad.Error

-- | Translate an expression to a term, and deappify it
trExpr :: CoreExpr -> HaloM Term'
trExpr e = deappify <$> trExpr' e

-- | Translate an expression to a term, but not deappified
trExpr' :: CoreExpr -> HaloM Term'
trExpr' e = do
    HaloEnv{..} <- ask
    let HaloConf{..} = conf
        isQuant x = x `S.elem` arities
        ty = exprType e

    monotype <- monoType ty

    case e of
        _ | exprIsBottom e -> bottom <$> monoType (exprType e)
        Var x
            | Just s <- M.lookup x skolems -> return s
            | isQuant x           -> return (qvar x)
            | TArr{} <- monotype  -> return (ptr x monotype)
            | otherwise           -> return (con x) -- constructor or CAF
        App e1 e2 -> app monotype <$> trExpr e1 <*> trExpr e2
        -- Int
        Lit (MachInt i)      -> return (litInteger i)
        -- Integer
        Lit (LitInteger i _) -> return (litInteger i)
        Cast e' _ -> trErr "cast"
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
