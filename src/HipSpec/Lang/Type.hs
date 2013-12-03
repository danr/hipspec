{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell #-}
-- | Types for the Rich and the Simple language
module HipSpec.Lang.Type where

import Data.Generics.Geniplate
import Data.List (nub,elemIndex,(\\))
import Data.Foldable (Foldable,toList)
import Data.Traversable (Traversable)
import Data.Function (on)

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Polymorphic types
data PolyType a = Forall [a] (Type a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Types
--   No higher-kinded type variables.
data Type a
    = TyVar a
    | ArrTy (Type a) (Type a)
    | TyCon a [Type a]
    | Integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

eqPolyType :: Eq a => PolyType a -> PolyType a -> Bool
eqPolyType (Forall xs t1) (Forall ys t2) = deBruijn xs t1 == deBruijn ys t2

eqType :: Eq a => Type a -> Type a -> Bool
eqType = (==) `on` deBruijn []

deBruijn :: Eq a => [a] -> Type a -> Type (Either Int a)
deBruijn = go
  where
    go g t0 = case t0 of
        ArrTy e1 e2 -> ArrTy (go g e1) (go g e2)
        TyCon a ts  -> TyCon (Right a) (map (go g) ts)
        TyVar x -> TyVar $ case elemIndex x g of
            Just n  -> Left n
            Nothing -> Right x
        Integer -> Integer

freePolyType :: Eq a => PolyType a -> [a]
freePolyType (Forall xs t) = freeTyVars t \\ xs

freeTyVars :: Eq a => Type a -> [a]
freeTyVars = nub . toList

makeArrows :: [Type a] -> Type a -> Type a
makeArrows xs t = foldr ArrTy t xs

transformType :: (Type a -> Type a) -> Type a -> Type a
transformType = $(genTransformBi 'transformType)

(///) :: Eq a => Type a -> a -> Type a -> Type a
t /// x = transformType $ \ t0 -> case t0 of
    TyVar y | x == y -> t
    _                -> t0

substManyTys :: Eq a => [(a,Type a)] -> Type a -> Type a
substManyTys xs t0 = foldr (\ (u,t) -> (t /// u)) t0 xs

collectArrTy :: Type a -> ([Type a],Type a)
collectArrTy (ArrTy t1 t2) =
    let (ts,t) = collectArrTy t2
    in  (t1:ts,t)
collectArrTy t = ([],t)


arrowResult :: String -> Type a -> Type a
arrowResult _ (ArrTy _ t) = t
arrowResult s _           = error $ s ++ ": not a function type"

