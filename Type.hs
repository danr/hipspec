{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell #-}
-- | Types for the Rich and the Simple language
module Type where

import Data.Generics.Geniplate
import Data.List (nub,union)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Function (on)

-- | Types
--
--   No higher-kinded type variables.
data Type a
    = TyVar a
    | ArrTy (Type a) (Type a)
    | TyCon a [Type a]
    | Forall a (Type a)

    | Star
    -- ^ Not used seriously
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

freeTyVars :: Eq a => Type a -> [a]
freeTyVars = go
  where
    go t = case t of
        TyVar x     -> [x]
        ArrTy t1 t2 -> go t1 `union` go t2
        TyCon _ ts  -> nub (concatMap go ts)
        Star        -> []
        Forall x t' -> filter (x /=) (go t')

data Typed a = (:::)
    { forget_type :: a
    , typed_type :: Type a
    }
  deriving (Show,Functor,Foldable,Traversable)

forget :: Functor f => f (Typed a) -> f a
forget = fmap forget_type

instance Eq a => Eq (Typed a) where
    (==) = (==) `on` forget_type

instance Ord a => Ord (Typed a) where
    compare = compare `on` forget_type

makeForalls :: [a] -> Type a -> Type a
makeForalls xs t = foldr Forall t xs

collectForalls :: Type a -> ([a],Type a)
collectForalls (Forall x t) =
    let (xs,t') = collectForalls t
    in  (x:xs,t')
collectForalls t = ([],t)

isForallTy :: Type a -> Bool
isForallTy Forall{} = True
isForallTy _        = False

transformType :: (Type a -> Type a) -> Type a -> Type a
transformType = $(genTransformBi 'transformType)

-- Unfortunately some code duplication here
(///) :: Eq a => Type a -> a -> Type a -> Type a
t /// x = transformType $ \ t0 -> case t0 of
    TyVar y | x == y -> t
    _                -> t0

substManyTys :: Eq a => [(a,Type a)] -> Type a -> Type a
substManyTys xs t0 = foldr (\ (u,t) -> (t /// u)) t0 xs

star :: Functor f => f a -> f (Typed a)
star = fmap (::: Star)

