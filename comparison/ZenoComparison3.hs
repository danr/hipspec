{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable #-}

module Main where

import Prelude (Bool(..),error,toEnum,fromEnum,pred,succ,sqrt,round
               ,Enum,Eq,Ord,Show,return,(.),undefined,div)
import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Data.Typeable

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized (\s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x))

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return

-- data Prop a = Equals a a --
type Prop a = a

infix 0 =:=

(=:=) :: a -> a -> Prop a
(=:=) = (=:=)

proveBool :: Bool -> Prop Bool
proveBool = (=:= True)

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)
data Tree a = Leaf | Node (Tree a) a (Tree a) deriving (Eq,Ord,Show,Typeable)

-- Boolean functions

max Z     y     = y             --
max x     Z     = x
max (S x) (S y) = S (max x y)

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

main = hipSpec "ZenoComparsion3.hs" conf 3
  where conf = describe "Nats"
               [ var "x"         natType
               , var "y"         natType
               , var "z"         natType
               , con "max"       max
               ]
           where
             natType  = (error "Nat type" :: Nat)


prop_47 :: Tree a -> Prop Nat
prop_47 a
  = (height (mirror a) =:= height a)

