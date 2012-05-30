{-# LANGUAGE GADTs,TypeFamilies,FlexibleInstances,FlexibleContexts,DeriveDataTypeable,ScopedTypeVariables,StandaloneDeriving #-}
module Test.QuickSpec.Term where

import Test.QuickSpec.CatchExceptions
import Control.Monad
import Data.Ord
import Data.Char
import Data.List
import Data.Maybe
import Data.Typeable
import System.Random
import Test.QuickCheck hiding (label)
import Test.QuickCheck.Gen

-- Terms.

data SymbolType = TVar | TConst deriving (Eq, Ord, Show)
data Symbol
  = Symbol { name :: String
           , description :: Maybe String
           , label :: Int
           , isUndefined :: Bool
           , typ :: SymbolType
           , range :: Gen Data
           }
  deriving Typeable

instance Show Symbol where
  show = name

instance Eq Symbol where
  e1 == e2 = label e1 == label e2

instance Ord Symbol where
  compare = comparing label

relabel :: Int -> Symbol -> Symbol
relabel l e = e { label = l }

describe :: String -> [Symbol] -> [Symbol]
describe str ss = map (\s -> s { description = Just str }) ss

isOp :: Symbol -> Bool
isOp s | typ s == TConst && name s == "[]" = False
isOp s | typ s == TConst = not (all (\x -> isAlphaNum x || x == '\'') (name s))
isOp _ = False

var :: forall a . (Classify a, Arbitrary a, Typeable a) => String -> a -> Symbol
var name _ = Symbol { name = name
                    , label = undefined
                    , description = Nothing
                    , isUndefined = False
                    , typ = TVar
                    , range = fmap Data (arbitrary :: Gen a)
                    }

con :: Classify a => String -> a -> Symbol
con name impl = Symbol { name = name
                       , label = undefined
                       , description = Nothing
                       , isUndefined = False
                       , typ = TConst
                       , range = fmap Data (return impl)
                       }

sym :: Symbol -> Term Symbol
sym elt = case typ elt of
            TVar -> Var elt
            TConst -> Const elt

data Term c = Const c | Var Symbol | App (Term c) (Term c) deriving (Typeable , Eq)

depth, size, numVars :: Term c -> Int
depth (App s t) = depth s `max` (1 + depth t)
depth _ = 1

size (App s t) = size s + size t
size (Var _) = 0
size _ = 1

numVars (Var _) = 1
numVars (Const _) = 0
numVars (App s t) = numVars s + numVars t

vars :: Term c -> [Symbol]
vars (App s t) = nub (vars s ++ vars t)
vars (Var s)   = [s]
vars _         = []

symbols :: Term Symbol -> [Symbol]
symbols (App s t) = nub (symbols s ++ symbols t)
symbols (Var s)   = [s]
symbols (Const s) = [s]

constants :: Term Symbol -> [Symbol]
constants (App s t) = nub (constants s ++ constants t)
constants (Var s)   = []
constants (Const s) = [s]

mapConsts :: (a -> b) -> Term a -> Term b
mapConsts f (Var v) = Var v
mapConsts f (Const c) = Const (f c)
mapConsts f (App t u) = App (mapConsts f t) (mapConsts f u)

joinConsts :: Term (Term a) -> Term a
joinConsts (Var v) = Var v
joinConsts (Const t) = t
joinConsts (App t u) = App (joinConsts t) (joinConsts u)

mapVars :: (Symbol -> Symbol) -> Term c -> Term c
mapVars f (Const k) = Const k
mapVars f (Var v)   = Var (f v)
mapVars f (App t u) = App (mapVars f t) (mapVars f u)

skeleton :: Term c -> Term c
skeleton (Var _) = Var (Symbol { label = 0, name = "*", typ = TVar })
skeleton (Const c) = Const c
skeleton (App t u) = App (skeleton t) (skeleton u)

subterms, directSubterms :: Term c -> [Term c]
subterms t = t:concatMap subterms (directSubterms t)
directSubterms (App t u) = [t, u]
directSubterms _ = []

instance Ord s => Ord (Term s) where
  s `compare` t = stamp s `compare` stamp t
   where
    stamp t = (depth t, size t, -occur t, top t, args t)

    occur t = length (vars t)

    top (Var s)   = Just (Left s)
    top (Const s) = Just (Right s)
    top _         = Nothing

    args (App s t) = [s, t]
    args _         = []

equationOrder (t, u) = (depth (ignoreFree t), size (ignoreFree t), depth t, size t, -(arity (termType t)), t, u)
  where occur = length . vars
        ignoreFree t | isFree t = Const (fun t)
        ignoreFree (App t u) = App (ignoreFree t) (ignoreFree u)
        ignoreFree t = t
        isFree (App t (Var s)) = isFree t && s `notElem` vars t
        isFree (Const s) = True
        isFree _ = False
        arity ty =
          case funTypes [ty] of
            [] -> 0
            [(_, ty')] -> 1 + arity ty'

instance Show (Term Symbol) where
  showsPrec p t = showString (showApp p (fun t) (args t))
   where
     brack s = "(" ++ s ++ ")"
     parenFun p s | p < 2 = s
                  | otherwise = brack s
     parenOp p s | p < 1 = s
                 | otherwise = brack s

     showApp p op [] | isOp op = brack (show op)
                     | otherwise = show op

     showApp p op [x] | isOp op =
       brack (show' 1 x ++ show op)

     showApp p op [x,y] | isOp op =
       parenOp p (show' 1 x ++ show op ++ show' 1 y)

     showApp p op (x:y:xs) | isOp op =
       parenFun p (concat (intersperse " " (brack (show' 1 x ++ show op ++ show' 1 y):map (show' 2) xs)))

     showApp p f xs =
       parenFun p (concat (intersperse " " (map (show' 2) (Const f:xs))))

     show' p x = showsPrec p x ""

deriving instance Show (Term Int)

fun :: Term Symbol -> Symbol
fun (App t u) = fun t
fun (Var x) = x
fun (Const x) = x

args :: Term a -> [Term a]
args (App t u) = args t ++ [u]
args x = []

-- Types.

funTypes :: [TypeRep] -> [(TypeRep, TypeRep)]
funTypes tys =
  [ (ty1, ty2) | ty <- tys,
                 (c, [ty1, ty2]) <- [splitTyConApp ty],
                 c == arr ]
  where (arr, _) = splitTyConApp (typeOf (undefined :: Int -> Int))

symbolClass :: Symbol -> Data
symbolClass s = unGen evalSym undefined undefined s

symbolType :: Symbol -> TypeRep
symbolType s =
  case symbolClass s of
    Data x -> typeOf x

termType :: Term Symbol -> TypeRep
termType (Var s) = symbolType s
termType (Const s) = symbolType s
termType (App t u) = fromJust (funResultTy (termType t) (termType u))

resultTypes :: TypeRep -> [TypeRep]
resultTypes ty = ty:concat [ resultTypes ty' | (_, ty') <- funTypes [ty] ]

isn'tFunction :: TypeRep -> Bool
isn'tFunction = null . funTypes . (:[])

allTypes :: [Symbol] -> [TypeRep]
allTypes ctx = nub (concatMap (resultTypes . symbolType) ctx)

-- Evaluation.

data Data where
  Data :: Classify a => a -> Data

evalSym :: Gen (Symbol -> Data)
evalSym = promote (\s -> label s `unaryVariant` range s)
  where unaryVariant :: Int -> Gen a -> Gen a
        unaryVariant n (MkGen f) = MkGen (\r s -> f (unarySplit n r) s)
        unarySplit 0 = fst . split
        unarySplit n = snd . split . unarySplit (n-1)

eval :: (Symbol -> Data) -> Term Symbol -> Data
eval ctx (Const s) = ctx s
eval ctx (Var s) = ctx s
eval ctx (App t u) =
  case (eval ctx t, eval ctx u) of
    (Data v, Data w) -> apply v w

class (Typeable a, Ord (Value a), Typeable (Value a)) => Classify a where
  type Value a
  evaluate :: a -> Gen (Value a)
  apply :: Typeable b => a -> b -> Data
  apply = error "ill-typed term formed"
  rhs :: a -> Data
  rhs = error "tried to get the rhs of a non-function"

  validSubstitution :: a -> [(Symbol,Term Symbol)] -> Bool
  validSubstitution _ _ = True

evalMap :: Classify a => ((a -> Value a) -> f a -> f (Value a)) -> f a -> Gen (f (Value a))
evalMap map x = do
  evalInside <- promote evaluate
  return (map evalInside x)

instance (Typeable a, Arbitrary a, Classify b) => Classify (a -> b) where
  type Value (a -> b) = Value b
  evaluate f = do
    x <- arbitrary
    evaluate (f x)
  apply f x =
    case cast x of
      Just x' -> Data (f x')
      Nothing -> error "ill-typed term formed"
  rhs f = Data (f undefined)

instance Classify Bool where
  type Value Bool = Bool
  evaluate = return

instance Classify Int where
  type Value Int = Int
  evaluate = return

instance Classify a => Classify (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  evaluate = evalMap fmap

instance Classify a => Classify [a] where
  type Value [a] = [Value a]
  evaluate = evalMap map

instance (Classify a, Classify b) => Classify (a, b) where
  type Value (a, b) = (Value a, Value b)
  evaluate (x, y) = liftM2 (,) (evaluate x) (evaluate y)

instance (Classify a, Classify b, Classify c) => Classify (a, b, c) where
  type Value (a, b, c) = (Value a, Value b, Value c)
  evaluate (x, y, z) = liftM3 (,,) (evaluate x) (evaluate y) (evaluate z)

data AnyValue where
  Value :: (Typeable a, Ord a) => a -> AnyValue
instance Eq AnyValue where
  x == y = x `compare` y == EQ
instance Ord AnyValue where
  Value x `compare` Value y =
    case cast x of
      Just x' -> x' `compare` y
      Nothing -> error "incomparable"

useSeed :: (StdGen, Int) -> (Symbol -> Data, Data -> AnyValue)
useSeed (g, n) = (unGen evalSym g1 n, f)
  where f d = case d of
                Data x -> Value (catchExceptions (unGen (evaluate x) g2 n))
        (g1, g2) = split g
