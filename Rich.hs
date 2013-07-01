{-# LANGUAGE DeriveFunctor #-}
-- | The Rich expression language, a subset of GHC Core
--
-- It is Rich because it has lambdas, let and cases at any level.
module Rich where

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
    | Lam a (Expr a)
    | Case (Expr a) a [Alt a]
    -- ^ Scrutinee expression, variable it is saved to, and the branches
    | Let [Function a] (Expr a)
  deriving (Eq,Ord,Show,Functor)

type Alt a = (Pattern a,Expr a)

-- | Patterns in branches
data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_ty_args :: [Type a]
        , pat_args    :: [a]
        }
    | LitPat Integer
  deriving (Eq,Ord,Show,Functor)

-- | Types
--
--   No higher-kinded type variables. Do we need this?
data Type a
    = TyVar a
    | ArrTy (Type a) (Type a)
    | TyCon a [Type a]
  deriving (Eq,Ord,Show,Functor)

