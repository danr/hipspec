{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell #-}
-- | The Rich expression language, a subset of GHC Core
--
-- It is Rich because it has lambdas, let and cases at any level.
module Rich where

import Data.Generics.Geniplate
import Data.List (union)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Type

{-# ANN module "HLint: ignore Use camelCase" #-}

data Program a = Program
    { prog_data  :: [Datatype a]
    , prog_fns   :: [Function a]
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Data definition
data Datatype a = Datatype
    { data_name    :: a
    , data_ty_args :: [a]
    , data_cons    :: [Constructor a]
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
    , fn_body    :: Expr a
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

mapFnBody :: (Expr a -> Expr a) -> Function a -> Function a
mapFnBody f fn = fn { fn_body = f (fn_body fn) }

-- | "Rich" expressions, includes lambda, let and case
data Expr a
    = Var a [Type a]
    -- ^ Variables applied to their type arguments
    | App (Expr a) (Expr a)
    | Lit Integer a
    -- ^ Integer literals
    --   The a is the type constructor
    | String a
    -- ^ String literals
    --   We semi-support them here to allow calls to error
    --   (pattern match failure also creates a string literal)
    --   The a is the type constructor
    | Lam a (Expr a)
    -- ^ Lam x t e t' means x :: t, and e :: t', i.e. the expression has type t -> t'
    | Case (Expr a) (Maybe a) [Alt a]
    -- ^ Scrutinee expression, variable it is saved to, the branches' types, and the branches
    --   This variable is mainly useful in Default branches
    --   It does not exist in the simple language, and
    --   it is sometimes inlined and then replaced with Nothing.
    | Let [Function a] (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

exprType :: Eq a => Expr (Typed a) -> Type a
exprType e0 = case e0 of
    Var v ts           -> appliedVarType v ts
    App e _            -> arrowResult "Rich.exprType" (exprType e)
    Lit _ (t ::: _)    -> TyCon t []
    String (t ::: _)   -> TyCon t []
    Lam (_ ::: t) e    -> ArrTy t (exprType e)
    Case _ _ alts      -> exprType (anyRhs "Rich.exprType" alts)
    Let _ e            -> exprType e

type Alt a = (Pattern a,Expr a)

anyRhs :: String -> [(b,a)] -> a
anyRhs _ ((_,e):_) = e
anyRhs s _         = error $ s ++ ": no alts in case"

-- | Patterns in branches
data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_ty_args :: [Type a]
        , pat_args    :: [a]
        }
    | LitPat Integer a
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

freeVars :: Eq a => Expr a -> [a]
freeVars = go
  where
    rm u = filter (/= u)
    rms us = filter (`notElem` us)

    go e0 = case e0 of
        Var u _       -> [u]
        App e1 e2     -> go e1 `union` go e2
        Lit{}         -> []
        String{}      -> []
        Lam u e       -> rm u (go e)
        Case e u alts -> go e `union` maybe id rm u (concatMap go' alts)
        Let fns e     -> rms (map bf fns) (concatMap (go . fb) fns `union` go e)

    go' (ConPat _ _ bs,rhs) = rms bs (go rhs)
    go' (Default,rhs)       = go rhs
    go' (LitPat{},rhs)      = go rhs

    bf (Function u _) = u
    fb (Function _ b) = b

letFree :: Expr a -> Bool
letFree = go
  where
    go e0 = case e0 of
        Var{}     -> True
        Lit{}     -> True
        String{}  -> True
        App e1 e2 -> go e1 && go e2
        Lam _ e   -> go e
        Let{}     -> False
        Case e _ alts -> go e && all (go . snd) alts

-- | Conservative guess of number of occurences for a variable (might overapproximate)
occurrences :: Eq a => a -> Expr a -> Int
occurrences x = go
  where
    go e0 = case e0 of
        Var y _ | x == y    -> 1
                | otherwise -> 0
        App e1 e2           -> go e1 + go e2
        Lam _ e             -> go e
        Case e _ alts       -> go e + sum (map (go . snd) alts)
        Let fns e           -> go e + sum (map (go . fn_body) fns)
        Lit{}               -> 0
        String{}            -> 0

-- | Does this variable occur in this expression?
--   Used to see if a function is recursive
occursIn :: Eq a => a -> Expr a -> Bool
occursIn x e = x `elem` freeVars e

transformExpr :: (Expr a -> Expr a) -> Expr a -> Expr a
transformExpr = $(genTransformBi 'transformExpr)

-- | Substitution, of simple variables (not applied to any types)
--
-- Since there are only have rank-1 types, bound variables from lambdas and
-- case never have an forall type and thus are not applied to any types.
(//) :: Eq a => Expr a -> a -> Expr a -> Expr a
e // x = transformExpr $ \ e0 -> case e0 of
    Var y [] | x == y -> e
    _                 -> e0

substMany :: Eq a => [(a,Expr a)] -> Expr a -> Expr a
substMany xs e0 = foldr (\ (u,e) -> (e // u)) e0 xs

-- | Substitution, of global variables (that can be applied to types)
--
-- Let-bound variables and top-level variables can have a forall-type.
-- Use this function to substitute such variables.
tySubst :: Eq a => a -> ([Type a] -> Expr a) -> Expr a -> Expr a
tySubst x k = transformExpr $ \ e0 -> case e0 of
    Var y tvs | x == y -> k tvs
    _ -> e0

apply :: Expr a -> [Expr a] -> Expr a
apply = foldl App

collectArgs :: Expr a -> (Expr a,[Expr a])
collectArgs (App e1 e2) =
    let (e,es) = collectArgs e1
    in  (e,es ++ [e2])
collectArgs e           = (e,[])

collectBinders :: Expr a -> ([a],Expr a)
collectBinders (Lam x e) =
    let (xs,e') = collectBinders e
    in  (x:xs,e')
collectBinders e         = ([],e)

findAlt :: Eq a => a -> [Type a] -> [Alt a] -> Maybe (Alt a)
findAlt x ts = go
  where
    go (alt@(ConPat x' ts' _,_):_)
        | x == x' && ts == ts' = Just alt
    go (_:xs) = go xs
    go []     = Nothing

makeLambda :: [a] -> Expr a -> Expr a
makeLambda xs e = foldr Lam e xs

findDefault :: [Alt a] -> Maybe (Alt a)
findDefault alts = case alts  of
    alt@(Default,_):_ -> Just alt
    _:xs              -> findDefault xs
    []                -> Nothing

