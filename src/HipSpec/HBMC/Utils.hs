{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs #-}
module HipSpec.HBMC.Utils where

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import HipSpec.Utils

import Data.Maybe
import Control.Monad.State hiding (lift)

mkLet :: Eq a => a -> Expr a -> Expr a -> Expr a
mkLet x ls e = Let [Function x (q (exprType' "mkLet" ls)) ls] e

ite :: Expr Id -> Expr Id -> Expr Id -> Expr Id
ite e t f = Case e Nothing [(pat ghcTrueId,t),(pat ghcFalseId,f)]
  where
    pat i = ConPat i (q boolType) [] []

findExpr :: (Expr a -> Bool) -> Expr a -> Bool
findExpr p = any p . universe

underLambda :: Functor m => (Expr a -> m (Expr a)) -> Expr a -> m (Expr a)
underLambda k b = makeLambda xs `fmap` k e
  where (xs,e) = collectBinders b

type Fresh = State Integer

fresh :: Fresh Integer
fresh = state (\ s -> (s,succ s))

hid :: HBMCId -> Id
hid = HBMCId

lift,liftTV :: Id
lift   = hid Lift
liftTV = hid LiftTV

newArg :: Fresh Id
newArg = Derived (Refresh $ hid Arg) <$> fresh

newRes :: Fresh Id
newRes = Derived (Refresh $ hid Res) <$> fresh

newCaser :: Fresh Id
newCaser = Derived (Refresh $ hid Caser) <$> fresh

unr :: Type Id -> Expr Id
unr t = Gbl (hid UNR) (Forall [x] (TyCon lift [TyVar x])) [t]
  where
    x = liftTV

the :: Expr Id -> Expr Id
the e = Gbl (hid The) (Forall [x] (TyVar x `ArrTy` TyCon lift [TyVar x])) [t] `App` e
  where
    x = liftTV
    t = exprType' "the" e

peek :: Expr Id -> Expr Id
peek e = Gbl (hid Peek) (Forall [x] (TyCon lift [TyVar x] `ArrTy` TyVar x)) [t] `App` e
  where
    x = liftTV
    t = case exprType' "peek" e of
        TyCon (HBMCId Lift) [t] -> t
        t' -> error $ "peek on " ++ ppShow e ++ " with type " ++ ppShow t'

tupleType :: Int -> PolyType Id
tupleType i = Forall tvs (tvs' `makeArrows` TyCon (hid $ TupleTyCon i) tvs')
  where
    tvs  = [ Lambda (hid $ TupleTyCon i) `Derived` fromIntegral z | z <- [0..i-1] ]
    tvs' = map TyVar tvs

selectType :: Int -> Int -> PolyType Id
selectType i j = Forall tvs (TyCon (hid $ TupleTyCon i) tvs' `ArrTy` (tvs' !! j))
  where
    tvs  = [ Lambda (hid $ TupleTyCon i) `Derived` fromIntegral z | z <- [0..i-1] ]
    tvs' = map TyVar tvs

argSat :: (Integer -> Bool) -> Id -> Bool
argSat p (Derived (Refresh (HBMCId Arg)) i) = p i
argSat _ _                                  = False

argId :: Id -> Bool
argId = argSat (const True)

argExpr :: Expr Id -> Bool
argExpr (Lcl i _) = argId i
argExpr _         = False

argExprSat :: (Integer -> Bool) -> Expr Id -> Bool
argExprSat p (Lcl i _) = argSat p i
argExprSat _ _         = False

