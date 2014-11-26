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

liftTy :: Type Id -> Type Id
liftTy t = TyCon lift [t]

refresh :: Id -> Integer -> Id
refresh = Derived . Refresh

newArg :: Fresh Id
newArg = refresh (hid Arg) <$> fresh

newRes :: Fresh Id
newRes = refresh (hid Res) <$> fresh

newCaser :: Fresh Id
newCaser = refresh (hid Caser) <$> fresh

label,d,constructor :: Id -> Id
label = hid . Label
d = hid . D
constructor = hid . Construct

hdata,con,val :: Id
hdata = hid Data
con = hid Con
val = hid Val
switch = hid Switch

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

unpty :: PolyType Id
unpty = error "Polytype destroyed by HBMC pass"

unty :: Type Id
unty = error "Type destroyed by HBMC pass"

ret ::  Expr Id -> Expr Id
ret e = Gbl (hid Return) unpty [unty] `app` e

tmp :: Fresh Id
tmp = (Derived (Refresh (hid Tmp))) <$> fresh

bind :: Expr Id -> Expr Id -> Fresh (Expr Id)
((Gbl (HBMCId Bind) _ _ `App` m) `App` f) `bind` g = do
    x <- tmp
    r <- (f `app` Lcl x unty) `bind` g
    m `bind` Lam x unty r

(Gbl (HBMCId Return) _ _ `App` a) `bind` (Lam x _ b) | occurrences x b <= 1 = return ((a // x) b)
m `bind` f = return (Gbl (hid Bind) unpty [unty,unty] `apply` [m,f])
