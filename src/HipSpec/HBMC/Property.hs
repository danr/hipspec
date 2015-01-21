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

trType :: Type Id -> Type Id
trType t@(_ `ArrTy` _) = error $ "Cannot handle exponential data types" ++ show t
trType (TyCon tc args) = TyCon (d tc) (map trType args)
trType TyVar{}         = thunkTy (TyCon (api "Bit") [])

hbmcLiteral :: DataInfo -> Literal -> Bool -> Mon [Stmt Id]
hbmcLiteral indexes (e1 :=: e2) pos = literal indexes e1 e2 pos
hbmcLiteral indexes (e1 :/: e2) pos = literal indexes e1 e2 (not pos)

literal :: DataInfo -> S.Expr Id -> S.Expr Id -> Bool -> Mon [Stmt Id]
literal indexes e1 e2 positive = do

    l <- lift (newTmp "l")
    r <- lift (newTmp "r")

    m1 <- monExpr (lcl l) (S.injectExpr e1)
    m2 <- monExpr (lcl r) (S.injectExpr e2)

    return
        [ BindExpr l Nothing (gbl new)
        , BindExpr r Nothing (gbl new)
        , StmtExpr m1
        , StmtExpr m2
        , StmtExpr $
           gbl (api (if positive then "notEqualHere" else "equalHere"))
            `apply`
              [lcl l,lcl r]
        ]

hbmcProp :: DataInfo -> Property -> Mon (Function Id)
hbmcProp indexes Property{..} = Function prop_id unpty <$> do

    let lits = (prop_goal `zip` repeat True) ++ (prop_assums `zip` repeat False)

    literals <-
      sequence
        [ hbmcLiteral indexes lit pos
        | (lit,pos) <- lits
        ]

    let values =
          [ BindExpr x (Just (trType t)) (gbl new)
          | (x,t) <- prop_vars
          ]

    res <- lift (newTmp "res")
    tpl <- lift (newTmp "tpl")

    return $
      mkDo
         ([ StmtExpr $ psl "Generating symbolic values..." ]
          ++ values ++
          [ StmtExpr $ psl "Generating problem..." ]
          ++ concat literals ++
          [ StmtExpr $ psl "Solving..."
          , bindExpr res (gbl (api "solve"))
          , StmtExpr $ gbl (api "io") `App` (gbl (prelude "print") `App` lcl res)
          ]
         )
         (gbl (api "ifTrue") `apply`
           [ lcl res
           , mkDo [bindExpr tpl (gbl genericGet `App` binTupleLit (map (lcl . fst) prop_vars))]
                  (gbl (api "io") `App` (gbl (prelude "print") `App` lcl tpl))
           ])

