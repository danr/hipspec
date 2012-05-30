{-# LANGUAGE FlexibleContexts, PatternGuards, ViewPatterns #-}

-- This module is a common interface to Types and StructuralInduction
-- Anything that needs to know the whole type environment

module Hip.Trans.TyEnv where

import Hip.Trans.Core
import Hip.Trans.ParserInternals
import Hip.Trans.Pretty
import Hip.Trans.Constructors
import Hip.Util

import Data.List hiding (partition)
import Data.Maybe (fromMaybe)
import Data.Generics.Uniplate.Data

import Control.Arrow
import Control.Monad
import Control.Monad.State

import qualified Hip.StructuralInduction as S

type ConName = Name
type TypeName = Name
type VarName = Name

type TyEnv = [(Name,[(Name,Type)])]

substType :: [(Name,Type)] -> Type -> Type
substType s = transform f
  where
    f (TyVar x) | Just t <- lookup x s = t
    f t                                = t

unTyVar :: Type -> Name
unTyVar (TyVar x) = x
unTyVar t         = error $ "unTyVar: " ++ show t

instantiate :: TyEnv -> Type -> Maybe [(Name,Type)]
instantiate env (TyCon n ts)
    | Just cons <- lookup n env = Just (map (uncurry inst) cons)
  where
    inst :: Name -> Type -> (Name,Type)
    inst n t = case resTy of
                   TyCon _ (map unTyVar -> as) ->
                       -- as is for instance ["a","b","c"]
                       -- ts could be [Nat,List a,b -> c]
                       let instMap = zip as ts
                       in  (n,foldr1 tapp [ substType instMap c | c <- argsTy ++ [resTy] ])
                   _  -> (n,t)
      where
        resTy   :: Type
        argsTy :: [Type]
        (argsTy,resTy) = case t of
                       TyApp xs -> (init xs,last xs)
                       _        -> ([],t)
instantiate _ _ = Nothing

translateEnv :: TyEnv -> S.TyEnv String Type
translateEnv env t = fmap (map (second argEnv)) (instantiate env t)
  where
    argEnv :: Type -> [S.Arg Type]
    argEnv t = let res  = resType t
                   args = argsTypes t
               in  map (arg res) args

    arg :: Type -> Type -> S.Arg Type
    arg t1 t@(TyApp{})    = S.Exp t (argsTypes t)
    arg t1 t2 | t1 == t2  = S.Rec t2
    arg t1 t2             = S.NonRec t2


