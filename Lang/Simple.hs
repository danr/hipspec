{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | The Simple expression language, a subset of GHC Core
--
-- It is Simple because it lacks lambdas, let and only allows a cascade of
-- cases at the top level.
--
-- There is some code duplication between this and the Rich
-- language. It is unclear how this could be remedied.
module Lang.Simple
    ( Function(..)
    , Body(..)
    , Alt
    , Expr(..)
    , collectArgs
    , apply
    , bodyType
    , exprType
    , module Lang.Rich
    , module Lang.Type
    , injectFn
    , injectBody
    , injectExpr
    ) where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

-- Patterns are resued from the rich language
import Lang.Rich (Pattern(..),anyRhs)
import qualified Lang.Rich as R
import Lang.Type

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
    = Var a [Type a]
    -- ^ Variables applied to their type arguments
    | App (Expr a) (Expr a)
    | Lit Integer a
    -- ^ The integer and its type constructor
    --   (to be able to infer the type)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

collectArgs :: Expr a -> (Expr a,[Expr a])
collectArgs (App e1 e2) =
    let (e,es) = collectArgs e1
    in  (e,es ++ [e2])
collectArgs e           = (e,[])

apply :: Expr a -> [Expr a] -> Expr a
apply = foldl App

bodyType :: Eq a => Body (Typed a) -> Type a
bodyType = R.exprType . injectBody

exprType :: Eq a => Expr (Typed a) -> Type a
exprType = R.exprType . injectExpr

-- * Injectors to the Rich language (for pretty-printing, linting)

injectFn :: Function a -> R.Function a
injectFn (Function f as b) = R.Function f (R.makeLambda as (injectBody b))

injectBody :: Body a -> R.Expr a
injectBody b0 = case b0 of
    Case e alts -> R.Case (injectExpr e) Nothing
                          [ (p,injectBody b) | (p,b) <- alts ]
    Body e      -> injectExpr e

injectExpr :: Expr a -> R.Expr a
injectExpr e0 = case e0 of
    Var x ts  -> R.Var x ts
    App e1 e2 -> R.App (injectExpr e1) (injectExpr e2)
    Lit l tc  -> R.Lit l tc

