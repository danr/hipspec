{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs, RecordWildCards #-}
module HipSpec.HBMC.Property where

import qualified Data.Foldable as F

import HipSpec.HBMC.Utils hiding (lift)

import HipSpec.Pretty

import HipSpec.Property

import HipSpec.HBMC.Monadic
import HipSpec.HBMC.Switch

import qualified HipSpec.Lang.Simple as S

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import Data.List
import HipSpec.Utils

import Data.Maybe
import Control.Monad
import Control.Monad.State

psl s = gbl (raw "io") `App` (gbl (raw "putStrLn") `App` String s)

newValue :: Integer -> Type Id -> Expr Id
newValue gbl_size t@(_ `ArrTy` _)  = error $ "Cannot handle exponential data types" ++ show t
newValue gbl_size (TyCon tc' args) = gbl (new tc') `apply` (Lit gbl_size:map (newValue gbl_size)args)
newValue gbl_size _                = gbl (raw "newNat") `App` Lit gbl_size

hbmcLiteral :: DataInfo -> Literal -> Mon (Expr Id)
hbmcLiteral indexes (e1 :=: e2) = do

    l <- lift (newTmp "l")
    r <- lift (newTmp "r")

    m1 <- lift . addSwitches indexes =<< monExpr (S.injectExpr e1)
    m2 <- lift . addSwitches indexes =<< monExpr (S.injectExpr e2)

    o <- lift $ bind m2 (Lam r unty $ gbl (raw "equal") `apply` map lcl [l,r])

    lift $ bind m1 (Lam l unty o)

infixr >>>

(>>>),(==>) :: Expr Id -> Expr Id -> Expr Id
e1 >>> e2 = gbl (raw ">>") `apply` [e1,e2]
e1 ==> e2 = gbl (raw "==>") `apply` [e1,listLit [e2]]

nt :: Expr Id -> Expr Id
nt e = gbl (raw "nt") `App` e

addBit :: Expr Id -> Expr Id
addBit b = addClause [b]

addClause :: [Expr Id] -> Expr Id
addClause bs = gbl (raw "addClause") `App` listLit bs

hbmcProp :: DataInfo -> Integer -> Property -> Mon (Function Id)
hbmcProp indexes gbl_size Property{..} = Function prop_id unpty <$> do
    let values e = lift $ foldM (\ acc (x,t) -> newValue gbl_size t `bind` Lam x unty acc) e prop_vars

    let lits = (prop_goal,nt):(prop_assums `zip` repeat id)

    let literals e = foldM
            (\ acc (lit,litf) -> do
                lexpr <- hbmcLiteral indexes lit
                lname <- lift (newTmp "l")
                lift $ lexpr `bind` Lam lname unty (addBit (litf (lcl lname)) >>> acc)
            )
            e lits


    let body = psl "Running solver..."
           >>> gbl (raw "check")
           >>> psl "Done!"
           >>> (gbl genericGet `App` (tuple (map (lcl . fst) prop_vars)))

    l <- (psl "Running functions..." >>>) <$> literals body

    (psl "Generating symbolic values..." >>>) <$> values l

