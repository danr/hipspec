{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | The Simple expression language, a subset of GHC Core
--
-- It is Simple because it lacks lambdas, let and only allows a cascade of
-- cases at the top level.
module Simple
    ( Function(..)
    , Body(..)
    , Alt
    , Expr(..)
    , collectArgs
    , apply
    , bodyType
    , exprType
    , module Rich
    ) where

-- Patterns, types and data types are resued from the rich language
import Rich (Pattern(..),Type(..),Typed(..),forget,substManyTys,collectForalls,makeForalls)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Function definition,
--   There are no lambdas so the arguments to the functions are declared here.
data Function a = Function
    { fn_name    :: a
    , fn_ty_args :: [a]
    , fn_type    :: Type a
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
    = Var a [Type a]
    -- ^ Variables applied to their type arguments
    | App (Expr a) (Expr a)
    | Lit Integer (Type a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

collectArgs :: Expr a -> (Expr a,[Expr a])
collectArgs (App e1 e2) =
    let (e,es) = collectArgs e1
    in  (e,es ++ [e2])
collectArgs e           = (e,[])

apply :: Expr a -> [Expr a] -> Expr a
apply = foldl App

bodyType :: Eq a => Body (Typed a) -> Type a
bodyType (Case _ ((_,b):_)) = bodyType b
bodyType (Body e)           = exprType e

exprType :: Eq a => Expr (Typed a) -> Type a
exprType e0 = case e0 of
    Var (x ::: ty) ts ->
        let (tvs,ty') = collectForalls ty
        in  substManyTys (zip tvs (map forget ts)) ty'
    App e1 e2         -> exprType e2
    Lit _ t           -> forget t

