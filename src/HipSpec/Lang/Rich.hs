{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
-- | The Rich expression language, a subset of GHC Core
--
-- It is Rich because it has lambdas, let and cases at any level.
module HipSpec.Lang.Rich where

import Data.Generics.Geniplate
import Data.List (nub)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import HipSpec.Lang.Type

{-# ANN module "HLint: ignore Use camelCase" #-}

data Program a = Program
    { prog_data  :: [Datatype a]
    , prog_fns   :: [Function a]
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Data definition
data Datatype a = Datatype
    { data_ty_con :: a
    , data_tvs    :: [a]
    , data_cons   :: [Constructor a]
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Constructor a = Constructor
    { con_name :: a
    , con_args :: [Type a]
    -- ^ Arguments to the constructor, /besides/ the type
    --   arguments that are bound in the data type
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Function definition
data Function a = Function
    { fn_name    :: a
    , fn_type    :: PolyType a
    , fn_body    :: Expr a
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

mapFnBody :: (Expr a -> Expr a) -> Function a -> Function a
mapFnBody f fn = fn { fn_body = f (fn_body fn) }

type Alt a = (Pattern a,Expr a)

-- | "Rich" expressions, includes lambda, let and case
data Expr a
    = Lcl a (Type a)
    -- ^ Local variables
    --   For now, we don't support polymorphic lets. :(
    | Gbl a (PolyType a) [Type a]
    -- ^ Global variables applied to their type arguments
    | App (Expr a) (Expr a)
    | Lit Integer
    -- ^ Integer literals
    --   The a is the type constructor
    | String String
    -- ^ String literals
    --   We semi-support them here to allow calls to error
    --   (pattern match failure also creates a string literal)
    | Lam a (Type a) (Expr a)
    -- ^ Lam x t e t' means x :: t, and e :: t', i.e. the expression has type t -> t'
    | Case (Expr a) (Maybe (a,Type a)) [Alt a]
    -- ^ Scrutinee expression, variable it is saved to, the branches' types, and the branches
    --   This variable is mainly useful in Default branches
    --   It does not exist in the simple language, and
    --   it is sometimes inlined and then replaced with Nothing.
    | Let [Function a] (Expr a)
    --   Local lets should be non-polymorphic for now, though it is not
    --   the type it gets here is too expressible. It does simplify,
    --   and if it is ever needed it could be added without too much of
    --   a hassle.
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Patterns in branches
data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_type    :: PolyType a
        , pat_ty_args :: [Type a]
        , pat_args    :: [(a,Type a)]
        }
    | LitPat Integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instanceUniverseBi  [t| forall a . (Expr a,Expr a) |]
instanceUniverseBi  [t| forall a . (Expr a,Type a) |]
instanceTransformBi [t| forall a . (Expr a,Expr a) |]
instanceTransformBi [t| forall a . (Expr a,[Function a]) |]
instanceTransformBi [t| forall a . (Expr a,Function a) |]

instanceUniverseBi  [t| forall a . (Datatype a,a) |]
instanceUniverseBi  [t| forall a . (Datatype a,Type a) |]

univExpr :: Expr a -> [Expr a]
univExpr = universeBi

typeUnivExpr :: Expr a -> [Type a]
typeUnivExpr = universeBi

transformExpr :: (Expr a -> Expr a) -> Expr a -> Expr a
transformExpr = transformBi

exprTyVars :: Eq a => Expr a -> [a]
exprTyVars e = nub [ a | TyVar a <- typeUnivExpr e ]

exprType :: Eq a => Expr a -> Type a
exprType e0 = case e0 of
    Lcl _ t                -> t
    Gbl _ (Forall xs t) ts -> substManyTys (zip xs ts) t
    App e _                -> arrowResult "Rich.exprType" (exprType e)
    Lit{}                  -> Integer
    String s               -> error $ "exprType: String: " ++ show s
    Lam _ t e              -> ArrTy t (exprType e)
    Case _ _ alts          -> exprType (anyRhs "Rich.exprType" alts)
    Let _ e                -> exprType e


anyRhs :: String -> [(b,a)] -> a
anyRhs _ ((_,e):_) = e
anyRhs s _         = error $ s ++ ": no alts in case"


-- | Free (local) variables
freeVars :: Eq a => Expr a -> [a]
freeVars = map fst . typedFreeVars

-- | Free, typed, (local) variables
typedFreeVars :: Eq a => Expr a -> [(a,Type a)]
typedFreeVars e = [ at | at@(a,_) <- lcls, a `notElem` bound ]
  where
    univ = univExpr e
    lcls = nub [ (a,t) | Lcl a t <- univ ]
    bound = nub $
        [ a | Lam a _ _  <- univ ] ++
        [ a | Case _ (Just (a,_)) _ <- univ ] ++
        [ a | Case _ _ alts <- univ, (ConPat _ _ _ as,_) <- alts, (a,_) <- as ] ++
        [ fn_name fn | Let fns _ <- univ, fn <- fns ]

letFree :: Expr a -> Bool
letFree e = and [ False | Let{} <- univExpr e ]

-- | Number of occurences for a (local) variable
occurrences :: Eq a => a -> Expr a -> Int
occurrences x e = length [ () | Lcl y _ <- univExpr e, x == y ]

-- | Does this variable occur in this expression?
--   Used to see if a function is recursive
occursIn :: Eq a => a -> Expr a -> Bool
occursIn x e = x `elem` freeVars e


-- | Substitution, of local variables
--
-- Since there are only have rank-1 types, bound variables from lambdas and
-- case never have an forall type and thus are not applied to any types.
(//) :: Eq a => Expr a -> a -> Expr a -> Expr a
e // x = transformExpr $ \ e0 -> case e0 of
    Lcl y _ | x == y -> e
    _                -> e0

substMany :: Eq a => [(a,Expr a)] -> Expr a -> Expr a
substMany xs e0 = foldr (\ (u,e) -> (e // u)) e0 xs

-- | Substitution, of global variables (that can be applied to types)
--
-- Let-bound variables and top-level variables can have a forall-type.
-- Use this function to substitute such variables.
tySubst :: Eq a => a -> ([Type a] -> Expr a) -> Expr a -> Expr a
tySubst x k = transformExpr $ \ e0 -> case e0 of
    Gbl y _ tys | x == y -> k tys
    _                    -> e0

apply :: Expr a -> [Expr a] -> Expr a
apply = foldl App

collectArgs :: Expr a -> (Expr a,[Expr a])
collectArgs (App e1 e2) =
    let (e,es) = collectArgs e1
    in  (e,es ++ [e2])
collectArgs e           = (e,[])

collectBinders :: Expr a -> ([(a,Type a)],Expr a)
collectBinders (Lam x t e) =
    let (xs,e') = collectBinders e
    in  ((x,t):xs,e')
collectBinders e         = ([],e)

findAlt :: Eq a => a -> [Type a] -> [Alt a] -> Maybe (Alt a)
findAlt x ts = go
  where
    go (alt@(ConPat x' _ ts' _,_):_)
        | x == x' && ts == ts' = Just alt
    go (_:xs) = go xs
    go []     = Nothing

makeLambda :: [(a,Type a)] -> Expr a -> Expr a
makeLambda xs e = foldr (uncurry Lam) e xs

findDefault :: [Alt a] -> Maybe (Alt a)
findDefault alts = case alts  of
    alt@(Default,_):_ -> Just alt
    _:xs              -> findDefault xs
    []                -> Nothing

