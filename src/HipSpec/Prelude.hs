{-# LANGUAGE OverlappingInstances, FlexibleInstances,FlexibleContexts,GADTs #-}
module HipSpec.Prelude
    (module Test.QuickCheck
    ,module Data.Typeable
    ,Prop
    ,(=:=)
    ,proveBool
    ,given
    ,givenBool
    ,(==>)
    ,oops) where

import Test.QuickCheck hiding (Prop, (==>))
import Data.Typeable

infix 1 =:=

infixr 0 ==>

data Prop a where
    Given :: Prop b -> Prop a -> Prop a
    (:=:) :: a -> a -> Prop a
    Oops :: Prop a -> Prop a

given :: Prop b -> Prop a -> Prop a
given = Given

givenBool :: Bool -> Prop a -> Prop a
givenBool b = Given (b =:= True)

(==>) :: Prop b -> Prop a -> Prop a
(==>) = Given

proveBool :: Bool -> Prop Bool
proveBool lhs = lhs =:= True

oops :: Prop a -> Prop a
oops = Oops

(=:=) :: a -> a -> Prop a
(=:=) = (:=:)

instance (Eq a,Show a,Arbitrary a,Testable (Prop b)) => Testable (Prop (a -> b)) where
  property (lhs :=: rhs) = forAll arbitrary $ \x -> property (lhs x :=: rhs x)
  property (Oops p)      = expectFailure (property p)

instance Eq a => Testable (Prop a) where
  property (lhs :=: rhs) = property (lhs == rhs)
  property (Oops p)      = expectFailure (property p)

instance Show (a -> b) where
  show _ = "<fun>"
