{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs, RecordWildCards #-}
module HipSpec.HBMC.Property where

import qualified Data.Foldable as F

import HipSpec.HBMC.Utils hiding (lift)

import HipSpec.Pretty

import HipSpec.Property

import HipSpec.HBMC.Prolog
import HipSpec.HBMC.Helpers

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

psl s = gbl (api "io") `App` (gbl (prelude "putStrLn") `App` String s)

newValue :: Type Id -> Expr Id
newValue _ = gbl new
{-
newValue t@(_ `ArrTy` _)  = error $ "Cannot handle exponential data types" ++ show t
newValue (TyCon tc' args) = gbl (new tc') `apply` (gbl_depth:map newValue args)
newValue _                = gbl (api "newNat") `App` gbl_depth
-}

hbmcLiteral :: DataInfo -> Literal -> Mon (Expr Id)
hbmcLiteral indexes (e1 :=: e2) = literal indexes e1 e2 True
hbmcLiteral indexes (e1 :/: e2) = literal indexes e1 e2 False

literal :: DataInfo -> S.Expr Id -> S.Expr Id -> Bool -> Mon (Expr Id)
literal indexes e1 e2 positive = do

    l <- lift (newTmp "l")
    r <- lift (newTmp "r")

    m1 <- {- lift . addSwitches indexes =<< -} monExpr (lcl l) (S.injectExpr e1)
    m2 <- {- lift . addSwitches indexes =<< -} monExpr (lcl r) (S.injectExpr e2)

    return
      (inSequence [m1,m2]
        (gbl
          (api
              (if positive then "equalHere" else "notEqualHere"))
            `apply`
              map lcl [l,r]))

hbmcProp :: DataInfo -> Property -> Mon (Function Id)
hbmcProp indexes Property{..} = Function prop_id unpty <$> do

    let lits = (prop_goal `zip` repeat nt) ++ (prop_assums `zip` repeat id)

    literals <- sequence
            [ hbmcLiteral indexes lit
            | (lit,litf) <- lits
            ]

    let values e =
          do e' <- lift $ foldM (\ acc (x,t) -> newValue t `bind` Lam x unty acc) e prop_vars
             return (psl "Generating symbolic values..." >>> e')

    values $ inSequence
        ( [ psl "Generating problem..." ]
          ++ literals ++
          [ psl "Solving..."
          , gbl (api "solve")
          , psl "Done!"
          ])
        (gbl genericGet `App` (tuple (map (lcl . fst) prop_vars)))

