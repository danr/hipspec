{-# LANGUAGE OverlappingInstances, FlexibleInstances, FlexibleContexts, GADTs #-}
module HipSpec
    ( module Test.QuickCheck
    , module QuickSpec.Signature
    , module Data.Typeable
    , module HipSpec
    ) where

import Test.QuickCheck hiding ((==>))
import QuickSpec.Signature
 {- hiding
    (names,Literal(..),Prop(..),typeOf,typeRep,Result,subterms,generate,TyCon,cast) -}
import Data.Typeable

infix 3 =:=
infix 3 =/=
infix 3 :=:
infix 3 :/:
infixr 2 /\
infixr :&:
infixr 1 \/
infixr :|:
infixr 0 ==>

data Prop where
    (:=:)  :: a -> a -> Prop
    (:/:)  :: a -> a -> Prop
    (:==>) :: Prop -> Prop -> Prop
    (:&:)  :: Prop -> Prop -> Prop
    (:|:)  :: Prop -> Prop -> Prop

(==>) :: Prop -> Prop -> Prop
(==>) = (:==>)

(=:=) :: a -> a -> Prop
(=:=) = (:=:)

(=/=) :: a -> a -> Prop
(=/=) = (:/:)

(\/) :: Prop -> Prop -> Prop
(\/) = (:|:)

(/\) :: Prop -> Prop -> Prop
(/\) = (:&:)

