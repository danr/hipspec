{-# LANGUAGE PatternGuards #-}
module Halo.MonoType where

import Var
import Type
import TyCon
import Control.Monad
import Halo.Shared

data MonoType t
    = TCon t -- only fully saturated type constructors for now
             -- (otherwise [MonoType t])
    | TArr (MonoType t) (MonoType t)
  deriving (Eq,Ord,Show)

type MonoType' = MonoType TyCon
    -- use tyConName to get the name of a tyCon
    -- (it's stored here in case the data constructors or the type is needed)
    --
infixr `TArr`

monoType :: Monad m => Type -> m MonoType'
monoType ty
    | Just (tc,[]) <- splitTyConApp_maybe ty = return (TCon tc) -- <$> mapM monoType ts
    | Just (t1,t2) <- splitFunTy_maybe ty    = TArr <$> monoType t1 <*> monoType t2
    | otherwise = fail $ "monoType: " ++ showOutputable ty ++ " is not a simple type!"
  where
    (<$>) = liftM
    (<*>) = ap

varMonoType :: Monad m => Var -> m MonoType'
varMonoType = monoType . varType

typeArgs :: MonoType t -> [MonoType t]
typeArgs (TArr t1 t2) = t1:typeArgs t2
typeArgs _            = []

resType :: MonoType t -> MonoType t
resType (TArr _ t2) = resType t2
resType t           = t

splitType :: MonoType t -> ([MonoType t],MonoType t)
splitType t = (typeArgs t,resType t)

arrowMonoType :: MonoType t -> Bool
arrowMonoType TArr{} = True
arrowMonoType _      = False

