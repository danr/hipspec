{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs #-}
module HipSpec.HBMC.Utils where

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import Data.List

import HipSpec.Utils

import Data.Maybe
import Control.Monad.State hiding (lift)

import qualified Data.Foldable as F

gbl_size_name :: String
gbl_size_name = "gbl_size"

gbl_size :: Expr Id
gbl_size = gbl (raw gbl_size_name)

gbl,lcl :: Id -> Expr Id
gbl i = Gbl i unpty []
lcl i = Lcl i unty

pat :: Id -> [Id] -> Pattern Id
pat p as = ConPat p unpty [] (as `zip` repeat unty)

nonZero :: Expr Id -> Expr Id
nonZero e = gbl (raw "/=") `apply` [e,Lit 0]

singletonIf :: Expr Id -> Expr Id -> Expr Id
singletonIf b e = ite b (listLit [e]) (listLit [])

append :: Expr Id -> Expr Id -> Expr Id
append e1 e2 = gbl (raw "++") `apply` [e1,e2]

concats :: [Expr Id] -> Expr Id
concats [] = listLit []
concats xs = foldr1 append xs

mkLet :: Eq a => a -> Expr a -> Expr a -> Expr a
mkLet x ls e = Let [Function x (q (exprType' "mkLet" ls)) ls] e

unaryCase :: Expr Id -> Id -> [Id] -> Expr Id -> Expr Id
unaryCase e k bound rhs = Case e Nothing [(pat k bound,rhs)]
    -- when bound = [], we don't really need to do this case (must be unit)
    -- when bound = [x], we could just inline (must be the singleton data type)

listLit :: [Expr Id] -> Expr Id
listLit []     = gbl realNil
listLit (e:es) = gbl realCons `apply` [e,listLit es]

-- When you know exactly how long list you want to case on
listCase :: Expr Id -> [Id] -> Expr Id -> Fresh (Expr Id)
listCase e []      rhs = return (nilCase e rhs)
listCase e (hd:xs) rhs = do
    tl <- newTmp "tl"
    consCase e hd tl <$> listCase (lcl tl) xs rhs

consCase :: Expr Id -> Id -> Id -> Expr Id -> Expr Id
consCase e h t rhs = Case e Nothing
    [ (pat realCons [h,t],rhs)
    , (pat realNil [],gbl realUndefined)
    ]

nilCase :: Expr Id -> Expr Id -> Expr Id
nilCase e rhs = Case e Nothing
    [ (pat realNil [],rhs)
    , (pat realCons [__,__],gbl realUndefined)
    ]

ite :: Expr Id -> Expr Id -> Expr Id -> Expr Id
ite e t f = Case e Nothing [(pat ghcTrueId,t),(pat ghcFalseId,f)]
  where
    pat i = ConPat i (q boolType) [] []

findExpr :: (Expr a -> Bool) -> Expr a -> Bool
findExpr p = any p . universe

underLambda :: Functor m => (Expr a -> m (Expr a)) -> Expr a -> m (Expr a)
underLambda k b = makeLambda xs `fmap` k e
  where (xs,e) = collectBinders b

underLambda' :: (Expr a -> Expr a) -> Expr a -> Expr a
underLambda' k b = makeLambda xs (k e)
  where (xs,e) = collectBinders b

type Fresh = State Integer

fresh :: Fresh Integer
fresh = state (\ s -> (s,succ s))

raw :: String -> Id
raw = hid . Raw

rawFor :: String -> Id -> Id
rawFor s i = hid (RawFor s i)

hid :: HBMCId -> Id
hid = HBMCId

lift,liftTV :: Id
lift   = raw "Lift"
liftTV = raw "a"

liftTy :: Type Id -> Type Id
liftTy t = TyCon lift [t]

refresh :: Id -> Integer -> Id
refresh = Derived . Refresh

newArg :: Fresh Id
newArg = newTmp "arg"

newRes :: Fresh Id
newRes = newTmp "res"

newCaser :: Fresh Id
newCaser = newTmp "caser"

newTmp :: String -> Fresh Id
newTmp s = (Derived (Refresh (raw s))) <$> fresh

tmp :: Fresh Id
tmp = newTmp "tmp"

realCons,realNil,realUndefined,__ :: Id
realCons = raw ":"
realNil  = raw "[]"
realUndefined = raw "undefined"
__ = raw "_"

tupleStruct :: Id
tupleStruct = raw "Tuple"

label,d,constructor,getForTyCon,argumentForTyCon,new :: Id -> Id
label = rawFor "Label"
d = rawFor "D"
constructor = rawFor "con"
getForTyCon = rawFor "get"
argumentForTyCon = rawFor "argument"
new = rawFor "new"


hdata,con,val,switch,genericGet,genericArgument :: Id
hdata = raw "Data"
con = raw "Con"
val = raw "val"
switch = raw "switch"
genericGet = raw "get"
genericArgument = raw "argument"

unr :: Type Id -> Expr Id
unr t = Gbl (raw "UNR") (Forall [x] (TyCon lift [TyVar x])) [t]
  where
    x = liftTV

the :: Expr Id -> Expr Id
the e = Gbl (raw "The") (Forall [x] (TyVar x `ArrTy` TyCon lift [TyVar x])) [t] `App` e
  where
    x = liftTV
    t = exprType' "the" e

peek :: Expr Id -> Expr Id
peek e = Gbl (raw "peek") (Forall [x] (TyCon lift [TyVar x] `ArrTy` TyVar x)) [t] `App` e
  where
    x = liftTV
    t = case exprType' "peek" e of
        TyCon (HBMCId (Raw "Lift")) [it] -> it
        t' -> error $ "peek on " ++ ppShow e ++ " with type " ++ ppShow t'

tuple :: [Expr Id] -> Expr Id
tuple args =
    Gbl (hid $ TupleCon n) (tupleType n)
        (map (exprType' "tuple") args) `apply` args
  where
    n = length args

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
argSat p (Derived (Refresh (HBMCId (Raw "arg"))) i) = p i
argSat _ _                                          = False

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
ret e = Gbl (raw "return") unpty [unty] `app` e

bind :: Expr Id -> Expr Id -> Fresh (Expr Id)
((Gbl (HBMCId (Raw ">>=")) _ _ `App` m) `App` f) `bind` g = do
    x <- tmp
    r <- (f `app` Lcl x unty) `bind` g
    m `bind` Lam x unty r

(Gbl (HBMCId (Raw "return")) _ _ `App` a) `bind` (Lam x _ b) | occurrences x b <= 1 = return ((a // x) b)
m `bind` f = return (Gbl (raw ">>=") unpty [unty,unty] `apply` [m,f])

renameFunctions :: [Function Id] -> [Function Id]
renameFunctions fns = map (rename [ (f,HBMCId (HBMC f)) | Function f _ _ <- fns ]) fns

checkFunctions :: [Function Id] -> [Function Id]
checkFunctions fns =
    [ Function f t $ (gbl (raw "check") >>>) `underLambda'` a
    | Function f t a <- fns
    ]

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

rename :: (Eq a,Functor f) => [(a,a)] -> f a -> f a
rename tbl = fmap (\ v -> fromMaybe v (lookup v tbl))

uniquifyWrt :: (Show a,Show b,Functor f,Monad m,F.Foldable f,Eq a,Eq b) => (a -> Maybe b) -> (a -> m a) -> f a -> m (f a)
uniquifyWrt surj new e
    | null dups = return e
    | otherwise = do
        new_names <- sequence [ (,) v `liftM` new v | v <- dups ]
        let new_e = rename new_names e
        uniquifyWrt surj new new_e
  where
    vars = nub (F.toList e)
    dups = nub [ v2
               | (v1,v2) <- uniqueCartesian vars
               , let s1 = surj v1, s1 == surj v2, s1 /= Nothing
               ]

uniquify :: (Functor f,F.Foldable f) => f Id -> Fresh (f Id)
uniquify = uniquifyWrt pp_id (\ x -> refresh x <$> fresh)
  where
    pp_id i
        | isJust (tryGetGHCTyCon i) = Nothing
        | HBMCId _ <- i = Nothing
        | otherwise = Just (ppId i)

