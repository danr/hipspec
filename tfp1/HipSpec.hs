{-# LANGUAGE OverlappingInstances, FlexibleInstances, FlexibleContexts, GADTs #-}
module HipSpec
    ( module Test.QuickCheck
    , module Data.Typeable
    , module Test.QuickSpec.Approximate
    , module Test.QuickSpec
    , Prop
    , (=:=)
    , proveBool
    , given
    , givenBool
    , total
    , (==>)
    , oops
    , Names
    , names
    ) where

import Test.QuickCheck hiding (Prop, (==>))
import Test.QuickSpec.Approximate
import Test.QuickSpec
import Data.Typeable

infix 1 =:=

infixr 0 ==>

data Prop a where
    Given :: Prop b -> Prop a -> Prop a
    (:=:) :: a -> a -> Prop a
    Oops  :: Prop a -> Prop a
    Total :: a -> Prop a

total :: a -> Prop a
total = Total

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

instance (Eq a,Show a,Show (a -> b),Arbitrary a,Testable (Prop b)) => Testable (Prop (a -> b)) where
  property (lhs :=: rhs) = forAll arbitrary $ \x -> property (lhs x :=: rhs x)
  property (Oops p)      = expectFailure (property p)
  property _             = error "Cannot test"

instance Eq a => Testable (Prop a) where
  property (lhs :=: rhs) = property (lhs == rhs)
  property (Oops p)      = expectFailure (property p)
  property _             = error "Cannot test"

class Names a where
    names :: a -> [String]

instance Names a => Names [a] where
    names ~[x] = map (++ "s") (names x)

instance (Names a,Names b) => Names (a,b) where
    names ~(x,y) = [ n ++ "_" ++ m | (n,m) <- zip (names x) (names y) ]

instance (Names a,Names b) => Names (Either a b) where
    names u = [ n ++ "__" ++ m | (n,m) <- zip (names x) (names y) ]
      where
        ~(Left x) = u
        ~(Right y) = u

instance Names a => Names (Maybe a) where
    names ~(Just x) = map ("m_" ++) (names x)

instance Names A where
    names _ = ["x","y","z"]

instance Names B where
    names _ = ["u","v","w"]

instance Names C where
    names _ = ["r","s","t"]

