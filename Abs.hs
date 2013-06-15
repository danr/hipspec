{-# LANGUAGE DeriveFunctor, EmptyDataDecls, KindSignatures, TypeOperators, FlexibleContexts, StandaloneDeriving #-}
{-|

    Abstract syntax, parameterised on the extra fancy
    stuff in the expressions and the variables.

    Two different representation share the same Expression data type

    The  expressions use an empty data type
    for extra stuff and only contain:

        * Var, App, Case, Literal integers

    They can be extended with Let and Lambda, and be
    removed by appropriate passes.

    All data types are functors, so the variables (including their
    type) can be modified with fmap.

    This file exports the rich expressions.  The Simple module
    reexports this module but replaces the Expr data type with the
    richer expressions.
-}
module Abs where

import Control.Applicative

{-
data Program e a = Program
    { prog_data :: [Datatype a]
    , prog_fns  :: [Function e a]
    }
    -}

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

-- | Function definition
--
-- Example:
--
--     const :: forall a b . a -> b -> c
--     const x y = y
--
-- Is represented by
--
--     Function
--        "const"
--        ["a","b"]
--        (a -> b -> c)
--        ["x","y"]
--        x
--
data Function b (e :: * -> *) a = Function
    { fn_name    :: a
    , fn_ty_args :: [a]
    , fn_type    :: Type a
    , fn_args    :: [a]
    , fn_body    :: b e a
    }
  deriving (Eq,Ord,Show,Functor)

test_simple :: Function TopCase Simple String
test_simple = Function "apa" ["a"] (TyVar "a") ["x"]
    $ Top $ Case (Var "x" [])
        [(Default, Top $ Case (Var "x" [])
            [(Default,Expr (Var "x" []))]
         )]

test_rich :: Function TopRich Rich String
test_rich = Function "apa" ["a"] (TyVar "a") ["x"]
    $ Rich $ InnerCase $
        Case
            (Extra $ InnerCase $ Case (Var "x" []) [])
        []

data TopCase e a
    = TopCase (Case TopCase Simple a)
    | Expr (Expr e a)
  deriving (Eq,Ord,Show,Functor)

data TopRich e a = Rich (Rich a)
  deriving (Eq,Ord,Show,Functor)

data Rich a
    = Lambda a (Expr Rich a)
    | InnerCase (Case TopRich Rich a)
    | Let [Function TopRich Rich a] (Expr Rich a)
  deriving (Eq,Ord,Show,Functor)

-- | Expressions with Let and Lambda
data Expr e a
    = Var a [a]
    -- ^ Variables applied to their type arguments
    | App (Expr e a) (Expr e a)
    | Lit Integer
    -- ^ Integer literals
    | Extra (e a)
  deriving (Eq,Ord,Show,Functor)

data Case b e a
    = Case (Expr e a) [(Pattern a,b e a)]
    -- ^ Invariant: Default patterns are always first(!)
  deriving (Eq,Ord,Show,Functor)

data Simple a deriving Functor

simple :: Simple a -> b
simple = error "simply magic!"

instance Show (Simple a) where
    show = simple

instance Eq (Simple a) where
    (==) = const simple

instance Ord (Simple a) where
    compare = const simple

-- | Patterns in branches
data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_ty_args :: [a]
        , pat_args    :: [a]
        }
    | IntPat Integer
  deriving (Eq,Ord,Show,Functor)

-- | Types
--
--   No higher-kinded type variables. Do we need this?
data Type a
    = TyVar a
    | ArrTy (Type a) (Type a)
    | TyCon a [Type a]
  deriving (Eq,Ord,Show,Functor)

