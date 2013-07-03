{-# LANGUAGE DeriveFunctor, DeriveFoldable, TemplateHaskell #-}
-- | The Rich expression language, a subset of GHC Core
--
-- It is Rich because it has lambdas, let and cases at any level.
module Rich where

import Data.Generics.Geniplate
import Data.Foldable (Foldable,toList)
import Data.List (nub,union)

{-# ANN module "HLint: ignore Use camelCase" #-}

data Program a = Program
    { prog_data  :: [Datatype a]
    , prog_fns   :: [Function a]
    }
  deriving (Eq,Ord,Show,Functor)

-- | Data definition
data Datatype a = Datatype
    { data_name    :: a
    , data_ty_args :: [a]
    , data_cons    :: [Constructor a]
    }
  deriving (Eq,Ord,Show,Functor)

data Constructor a = Constructor
    { con_name :: a
    , con_args :: [Type a]
    -- ^ Arguments to the constructor, /besides/ the type
    --   arguments that are bound in the data type
    }
  deriving (Eq,Ord,Show,Functor)

-- | Types
--
--   No higher-kinded type variables. Do we need this?
data Type a
    = TyVar a
    | ArrTy (Type a) (Type a)
    | TyCon a [Type a]
  deriving (Eq,Ord,Show,Functor,Foldable)

freeTyVars :: Eq a => Type a -> [a]
freeTyVars = nub . toList

-- | Function definition
data Function a = Function
    { fn_name    :: a
    , fn_ty_args :: [a]
    , fn_type    :: Type a
    , fn_body    :: Expr a
    }
  deriving (Eq,Ord,Show,Functor)

-- | "Rich" expressions, includes lambda, let and case
data Expr a
    = Var a [Type a]
    -- ^ Variables applied to their type arguments
    | App (Expr a) (Expr a)
    | Lit Integer
    -- ^ Integer literals
    | String
    -- ^ String literals
    --   We semi-support them here to allow calls to error
    --   (pattern match failure also creates a string literal)
    | Lam a (Type a) (Expr a) (Type a)
    -- ^ Lam x t e t' means x :: t, and e :: t', i.e. the expression has type t -> t'
    | Case (Expr a) a (Type a) [Alt a]
    -- ^ Scrutinee expression, variable it is saved to, the branches' types, and the branches
    --   This variable is mainly useful in Default branches
    --   It does not exist in the simple language.
    --   The type is needed if this case is lifted to the top level.
    | Let [Function a] (Expr a)
  deriving (Eq,Ord,Show,Functor)

type Alt a = (Pattern a,Expr a)

-- | Patterns in branches
data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_ty_args :: [Type a]
        , pat_args    :: [(a,Type a)]
        }
    | LitPat Integer
  deriving (Eq,Ord,Show,Functor)

freeVars :: Eq a => Expr a -> [a]
freeVars = go
  where
    rm u = filter (/= u)
    rms us = filter (`notElem` us)

    go e0 = case e0 of
        Var u _         -> [u]
        App e1 e2       -> go e1 `union` go e2
        Lit{}           -> []
        String          -> []
        Lam u _ e _     -> rm u (go e)
        Case e u _ alts -> go e `union` rm u (concatMap go' alts)
        Let fns e       -> rms (map bf fns) (concatMap (go . fb) fns `union` go e)

    go' (ConPat _ _ bs,rhs) = rms (map fst bs) (go rhs)
    go' (Default,rhs)       = go rhs
    go' (LitPat{},rhs)      = go rhs

    bf (Function u _ _ _) = u
    fb (Function _ _ _ b) = b


-- | Does this variable occur in this expression?
--   Used to see if a function is recursive
occursIn :: Eq a => a -> Expr a -> Bool
occursIn x e = x `elem` freeVars e

transformExpr :: (Expr a -> Expr a) -> Expr a -> Expr a
transformExpr = $(genTransformBi 'transformExpr)

-- | Substitution, substitutes a variable (not applied to any types) for an expression
--   TODO: What to do when it has types applied to it? Any examples?
(//) :: Eq a => Expr a -> a -> Expr a -> Expr a
e // x = transformExpr $ \ e0 -> case e0 of
    Var y [] | x == y -> e
    _                 -> e0

substMany :: Eq a => [(a,Expr a)] -> Expr a -> Expr a
substMany xs e0 = foldr (\ (u,e) -> (e // u)) e0 xs

tySubst :: Eq a => a -> ([Type a] -> Expr a) -> Expr a -> Expr a
tySubst x k = transformExpr $ \ e0 -> case e0 of
    Var y tvs | x == y -> k tvs
    _ -> e0

apply :: Expr a -> [Expr a] -> Expr a
apply e (x:xs) = apply (App e x) xs
apply e []     = e

collectArgs :: Expr a -> (Expr a,[Expr a])
collectArgs (App e1 e2) =
    let (e,es) = collectArgs e1
    in  (e,es ++ [e2])
collectArgs e           = (e,[])

collectBinders :: Expr a -> ([(a,Type a)],Expr a)
collectBinders (Lam x t e _) =
    let (xs,e') = collectBinders e
    in  ((x,t):xs,e')
collectBinders e         = ([],e)

lambdaBodyType :: Type a -> Expr a -> Type a
lambdaBodyType _ (Lam _ _ e t') = lambdaBodyType t' e
lambdaBodyType t _              = t

findAlt :: Eq a => a -> [Type a] -> [Alt a] -> Maybe (Alt a)
findAlt x ts alts = go alts
  where
    go (alt@(ConPat x' ts' _,_):_)
        | x == x' && ts == ts' = Just alt
    go (_:xs) = go xs
    go []     = Nothing

makeLambda :: [(a,Type a)] -> Expr a -> Type a -> (Expr a,Type a)
makeLambda []         e t' = (e,t')
makeLambda ((x,t):xs) e t' =
    let (e',t'') = makeLambda xs e t'
    in  (Lam x t e' t'',ArrTy t t'')

findDefault :: [Alt a] -> Maybe (Alt a)
findDefault alts = case alts  of
    alt@(Default,_):_ -> Just alt
    _:xs              -> findDefault xs
    []                -> Nothing

