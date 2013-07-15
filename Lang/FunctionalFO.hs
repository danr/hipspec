{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | The Functional First Order language. Explicitly typed.
--
--   ArrTy in the Type really means defunctionalised Type
module Lang.FunctionalFO where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Lang.Type

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Function definition,
--   There are no lambdas so the arguments to the functions are
--   declared here.
data Function a = Function
    { fn_name    :: a
    , fn_tvs     :: [a]
    , fn_args    :: [(a,Type a)]
    , fn_res_ty  :: Type a
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
    = Fun a [Type a] [Expr a]
    -- ^ Function (fully) applied to type arguments and arguments
    | App (Type a) (Type a) (Expr a) (Expr a)
    -- ^ Defunctionalisated application
    | Ptr a [Type a]
    -- ^ Pointer (applied to some types)
    | Lit Integer
    -- ^ The integer and its type constructor
    --   (to be able to infer the type)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Pattern a
    = Default
    | ConPat
        { pat_con     :: a
        , pat_ty_args :: [Type a]
        , pat_args    :: [(a,Type a)]
        }
    | LitPat Integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

partitionAlts :: [Alt a] -> (Maybe (Body a),[Alt a])
partitionAlts alts = case alts of
    (Default,rhs):xs -> (Just rhs,xs)
    alt:xs           -> let (mb,xs') = partitionAlts xs
                        in  (mb,alt:xs')
    []               -> (Nothing,[])

