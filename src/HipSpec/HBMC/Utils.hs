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

import qualified Id as GHC
import qualified GHC as GHC
import qualified IdInfo as GHC
import HipSpec.GHC.Utils

import Debug.Trace

prelude :: String -> Id
-- prelude s = raw s
prelude s = raw ("Prelude." ++ s)

api :: String -> Id
-- api s = raw s
api s = raw ("Prolog." ++ s)

gbl_depth_name :: String
gbl_depth_name = "gbl_depth"

gbl_depth :: Expr Id
gbl_depth = gbl (raw gbl_depth_name)

gbl,lcl :: Id -> Expr Id
gbl i = Gbl i unpty []
lcl i = Lcl i unty

pat :: Id -> [Id] -> Pattern Id
pat p as = ConPat p unpty [] (as `zip` repeat unty)

nonZero :: Expr Id -> Expr Id
nonZero e = gbl (prelude "/=") `apply` [e,Lit 0]

singletonIf :: Expr Id -> Expr Id -> Expr Id
singletonIf b e = ite b (listLit [e]) (listLit [])

append :: Expr Id -> Expr Id -> Expr Id
append e1 e2 = gbl (prelude "++") `apply` [e1,e2]

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
listLit = ListLit
{-
listLit []     = gbl realNil
listLit (e:es) = gbl realCons `apply` [e,listLit es]
-}

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
lift   = api "Lift"
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
realUndefined = prelude "undefined"
__ = raw "_"

tupleStruct :: Id
tupleStruct = api "Tuple"

label,d,mkCon,predCon,getForTyCon,argumentForTyCon :: Id -> Id
label = rawFor "Label"
d = rawFor "D"
predCon = rawFor "pred"
mkCon = rawFor "mk"
isCon = rawFor "is"
getForTyCon = rawFor "get"
argumentForTyCon = rawFor "argument"

new,choice,postpone :: Id
new = api "new"
choice = api "choice"
postpone = api "postpone"

equalHere,notEqualHere :: Id
equalHere = api "equalHere"
notEqualHere = api "notEqualHere"

(===),(=/=) :: Expr Id -> Expr Id -> Expr Id
u === v = gbl equalHere `apply` [u,v]
u =/= v = gbl notEqualHere `apply` [u,v]

hdata,con,val,switch,genericGet,genericArgument :: Id
hdata = api "Data"
con = api "con"
val = api "val"
switch = api "switch"
genericGet = api "get"
genericArgument = api "argument"

(=?) :: Expr Id -> Id -> Expr Id
label =? con = gbl (api "=?") `apply` [label,gbl (d con)]

thunk,force,peek,delay,this :: Id
thunk = api "Thunk"
delay = api "delay"
this  = api "this"
peek  = api "peek"
force = api "force"
must  = api "must"

thunkTy :: Type Id -> Type Id
thunkTy t = TyCon thunk [t]

errorf :: String -> Expr Id
errorf s = gbl (prelude "error") `App` String s

noopId :: Id
noopId = api "noop"

noop :: Type Id -> Expr Id
noop t = Gbl noopId (Forall [] t) []

-- binTupleType [t1,t2,t3,t4] = (t1,(t2,(t3,t4)))
binTupleType :: [Type Id] -> Type Id
binTupleType []     = TyCon (hid (TupleTyCon 0)) []
binTupleType [x]    = x
binTupleType (x:xs) = TyCon (hid (TupleTyCon 2)) [x,binTupleType xs]

binTupleLit :: [Expr Id] -> Expr Id
binTupleLit []     = tuple []
binTupleLit [x]    = x
binTupleLit (x:xs) = tuple [x,binTupleLit xs]

-- When you know exactly how long list you want to case on
binTupleCase :: Expr Id -> [Id] -> Expr Id -> Fresh (Expr Id)
binTupleCase e []      rhs = return rhs
binTupleCase e [x]     rhs = return ((e // x) rhs)
binTupleCase e (hd:xs) rhs = do
    tl <- newTmp "r"
    rhs' <- binTupleCase (lcl tl) xs rhs
    return $ Case e Nothing [ (pat (hid (TupleTyCon 2)) [hd,tl],rhs') ]

{-
the :: Expr Id -> Expr Id
the e = Gbl (api "The") (Forall [x] (TyVar x `ArrTy` TyCon lift [TyVar x])) [t] `App` e
  where
    x = liftTV
    t = exprType' "the" e

peek :: Expr Id -> Expr Id
peek e = Gbl (api "peek") (Forall [x] (TyCon lift [TyVar x] `ArrTy` TyVar x)) [t] `App` e
  where
    x = liftTV
    t = case exprType' "peek" e of
        TyCon i [it] | i == lift -> it
        t' -> error $ "peek on " ++ ppShow e ++ " with type " ++ ppShow t'
-}

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
ret e = Gbl (prelude "return") unpty [unty] `app` e

infixr >>>

(>>>) :: Expr Id -> Expr Id -> Expr Id
Do s1 u >>> Do s2 v = Do (s1 ++ [StmtExpr u] ++ s2) v
u       >>> Do s2 v = Do ([StmtExpr u] ++ s2) v
Do s1 u >>> v       = Do (s1 ++ [StmtExpr u]) v
u       >>> v       = Do [StmtExpr u] v

inSequence :: [Expr Id] -> Expr Id -> Expr Id
inSequence as a = foldr (>>>) a as

bind :: Id -> Expr Id -> Expr Id -> Fresh (Expr Id)
bind x m e2 = return (rawBind x m e2)

rawBind :: Id -> Expr Id -> Expr Id -> Expr Id
rawBind x (Do s1 u) (Do s2 v) = Do (s1 ++ [BindExpr x u] ++ s2) v
rawBind x u         (Do s2 v) = Do ([BindExpr x u] ++ s2) v
rawBind x (Do s1 u) v         = Do (s1 ++ [BindExpr x u]) v
rawBind x u         v         = Do [BindExpr x u] v

renameFunctions :: [Function Id] -> [Function Id]
renameFunctions fns = map (rename [ (f,HBMCId (HBMC f)) | Function f _ _ <- fns ]) fns

isRecursive :: Function Id -> Bool
isRecursive (Function f _ a) = or [ g == f | Gbl g _ _ <- universeBi a ]

{-
checkFunctions :: (Id -> Bool) -> [Function Id] -> [Function Id]
checkFunctions p fns =
    [ Function f t $ check `underLambda'` a
    | Function f t a <- fns
    , let check | p f
                = (gbl (api "postpone") `App`)
                | otherwise    = id
    ]
-}

(==>) :: Expr Id -> Expr Id -> Expr Id
e1 ==> e2 = gbl (api "==>") `apply` [e1,listLit [e2]]

nt :: Expr Id -> Expr Id
nt e = gbl (api "nt") `App` e

addBit :: Expr Id -> Expr Id
addBit b = addClause [b]

addClause :: [Expr Id] -> Expr Id
addClause bs = gbl (api "addClause") `App` listLit bs

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

replaceEquality :: TransformBi (Expr Id) t => t -> t
replaceEquality = transformBi $ \ e0 -> case e0 of
    (Gbl (HBMCId (HBMC x)) _ _ `App` e1) `App` e2 -> case originalId x of
        "$c==" -> Gbl (api "ifeq")
                    (q (makeArrows [proverBoolType,proverBoolType,exprType' "$c==" e1,exprType' "$c==" e2]
                                   proverBoolType))
                    [] `apply` [ghcTrue,ghcFalse,e1,e2]
        _      -> e0
         {-
        case tryGetGHCVar x of
            Just i  -> do
                print i
                print (GHC.isDictonaryId i)
                print (GHC.isDictId i)
                print (GHC.isDictId i)
--                putStrLn (showOutputable (GHC.idInfo i))
                putStrLn (showOutputable (GHC.idDetails i))
            Nothing -> return ()
        return e0
        -}
    _ -> e0

mkLets :: [((Id,Type Id),Expr Id)] -> Expr Id -> Expr Id
mkLets (((i,t),b@Lcl{}):es) e = mkLets es ((b // i) e)
mkLets (((i,t),b)      :es) e = Let [Function i (Forall [] t) b] (mkLets es e)
mkLets [] e = e

-- Removes dead lets and inlines silly lets
simpleLetOpt :: TransformBi (Expr Id) t => t -> t
simpleLetOpt = transformBi $
  \ (e0 :: Expr Id) ->
    case e0 of
      Let [Function f _ b] e
        | occurrences f e == 0 -> e
        | Lcl f' _ <- e, f == f' -> b

      _ -> e0


-- let t = T2 e1 e2 in E[proj1 t, proj2 t, t]
-- ~>
-- let u = e1
-- let v = e2
-- in  E[u,v,T2 u v]
untuple :: TransformBiM Fresh (Expr Id) t => t -> Fresh t
untuple = transformBiM $
  \ e0 ->
    case e0 of
      Let [Function t _ b] e
        | Just cs <- tupleCase b
        -> do us <- sequence
                [ do u <- newTmp "u"
                     return ((u,exprType' "untuple" c),c)
                | c <- cs
                ]
              let uvs = [ Lcl u ty | ((u,ty),_) <- us ]
              return $ mkLets us ((tuple uvs // t) (unproj t uvs e))
      _ -> return e0

-- case should be only variable for this to be effective
--
-- case a of
--   ...
--   case b of
--     ...
--     case c of
--     ... -> T2 e1 e2
--
--  (all branches return a tuple ... or noop)
--
--  =>
--
-- case a of
--   ...
--   case b of
--     ...
--     case c of
--     ... -> ei
--
--  for i=1 and i=2
--
tupleCase :: Expr Id -> Maybe [Expr Id]

tupleCase e0@(Gbl hid (Forall [] (TyCon (HBMCId (TupleTyCon _)) ts)) _)
  | hid == noopId
  = Just (map noop ts)

tupleCase (collectArgs -> (Gbl (HBMCId (TupleCon n)) _ tys,es))
  | n == length tys
  , n == length es
  = Just es

tupleCase (Case es mx alts) =
  do altss <- sequence
       [ do es <- tupleCase e
            return [ (p,e') | e' <- es ]
       | (p,e) <- alts
       ]
     return [ Case es mx alts | alts <- transpose altss ]

tupleCase _ = Nothing

unproj :: Id -> [Expr Id] -> Expr Id -> Expr Id
unproj t us = transform $
  \ e0 ->
    case e0 of
      Gbl (HBMCId (Select _ i)) _ _ `App` Lcl t' _ | t == t' -> us !! i
      _ -> e0

