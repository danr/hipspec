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

import Test.QuickCheck

type ConName = Name
type VarName = Name
type TypeName = Name

type TyEnv = [(TypeName,[(Name,Type)])]

testEnv :: TyEnv
testEnv = map (declName &&& conTypes) $ parseDecls $ concatMap (++ ";")
  [ "data Tree a = Branch (Tree a) a (Tree a) | Empty"
  , "data T = B T T | E"
  , "data Nat = Suc Nat | Zero"
  , "data List a = Cons a (List a) | Nil"
  , "data Expr = Add Expr Expr | Mul Expr Expr | Value Nat | X | Neg Expr"
  , "data Integ = PS Nat | NS Nat | Z"
  , "data Tup a b = Tup a b"
  , "data Either a b = Left a | Right b"
  , "data Bool = True | False"
  , "data Maybe a = Just a | Nothing"
  , "data Unit = Unit"
  , "data Ord = Zero | Suc Ord | Lim (Nat -> Ord)"
  , "data WrapList a = Wrap (List a)"
  , "data Z = P Nat | N Nat"
  , "data Even = Zero | ESucc Odd"
  , "data Odd = OSucc Even"
  , "data T a = B (T (Tup a a)) | V a"
  , "data Phantom a = Phantom"
  ]

substType :: [(Name,Type)] -> Type -> Type
substType s = transform f
  where
    f (TyVar x) | Just t <- lookup x s = t
    f t                                = t

unTyVar :: Type -> Name
unTyVar (TyVar x) = x
unTyVar t         = error $ "unTyVar: " ++ show t

bottomless :: Expr -> Bool
bottomless e = and [ False | Var x <- universe e, x == bottomName ]

instantiate :: Type -> TyEnv -> Maybe [(Name,Type)]
instantiate (TyCon n ts) env
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

