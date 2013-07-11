{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | The Functional First Order language
module FunctionalFO where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Function (on)

import qualified Rich as R

import Type hiding ((:::),forget_type)
import qualified Type as T

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Function definition,
--   There are no lambdas so the arguments to the functions are
--   declared here.
data Function a = Function
    { fn_name    :: a
    , fn_args    :: [a]
    , fn_body    :: Body a
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | The body of a function: cascades of cases, with branches eventually ending
--   in expressions.
data Body a
    = Case (Expr a) [Alt a]
    | Body (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Alt a = (Pattern a,Body a)

-- | The simple expressions allowed here
data Expr a
    = Apply a [FOType a] [Expr a]
    -- ^ Function (fully) applied to type arguments and arguments
    | Lit Integer a
    -- ^ The integer and its type constructor
    --   (to be able to infer the type)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Eq and Ord instances on the variable name
data FOTyped a = (:::)
    { forget_type :: a
    , typed_type  :: FOType a
    }
  deriving (Show,Functor,Foldable,Traversable)

data FOType a = FOType
    [a]      -- ^ Type variables
    [Type a] -- ^ Argument types
    (Type a) -- ^ Result type
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Eq a => Eq (FOTyped a) where
    (==) = (==) `on` forget_type

instance Ord a => Ord (FOTyped a) where
    compare = compare `on` forget_type

data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_ty_args :: [FOType a]
        , pat_args    :: [a]
        }
    | LitPat Integer a
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

toType :: FOType a -> Type a
toType (FOType tvs as r) = makeForalls tvs (makeArrows as r)

toTyped :: FOTyped a -> Typed a
toTyped (v ::: t) = v T.::: toType t

bodyType :: Eq a => Body (FOTyped a) -> Type a
bodyType = R.exprType . fmap toTyped . injectBody

exprType :: Eq a => Expr (FOTyped a) -> Type a
exprType = R.exprType . fmap toTyped . injectExpr

-- * Injectors to the Rich language (for pretty-printing, linting)

injectFn :: Function a -> R.Function a
injectFn (Function f as b) = R.Function f (R.makeLambda as (injectBody b))

injectBody :: Body a -> R.Expr a
injectBody b0 = case b0 of
    Case e alts -> R.Case (injectExpr e) Nothing
                          [ (injectPat p,injectBody b) | (p,b) <- alts ]
    Body e      -> injectExpr e

injectPat :: Pattern a -> R.Pattern a
injectPat p = case p of
    Default        -> R.Default
    LitPat x t     -> R.LitPat x t
    ConPat c ts as -> R.ConPat c (map toType ts) as

injectExpr :: Expr a -> R.Expr a
injectExpr e0 = case e0 of
    Apply x ts es -> R.apply (R.Var x (map toType ts)) (map injectExpr es)
    Lit l tc      -> R.Lit l tc

type Var a = FOTyped (FOName a)

data FOName a = Orig a | Ptr a | App | X | Y
  deriving (Eq,Ord,Show,Functor)

