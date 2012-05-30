{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable #-}

module Main where

import Prelude (Bool(..),error,toEnum,fromEnum,pred,succ,sqrt,round
               ,Enum,Eq,Ord,Show,return,(.),undefined)
import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Data.Typeable

main = hipSpec "CountRev.hs" conf 3
  where conf = describe "Nats"
               [ var "x"         elemType
               , var "y"         elemType
               , var "z"         elemType
               , var "xs"        listType
               , var "ys"        listType
               , var "zs"        listType
               , con "[]"        ([]    :: [Nat])
               , con ":"         ((:)   :: Nat  -> [Nat] -> [Nat])
               , con "++"        ((++)  :: [Nat] -> [Nat] -> [Nat])
               , con "count"     (count :: Nat -> [Nat] -> Nat)
               , con "rev"       (rev   :: [Nat] -> [Nat])
               , con "=="        (==)
               , con "True"      True
               , con "Z"         Z
               , con "S"         S
               , con "+"         (+)
               ]
           where
             elemType  = (error "Elem type" :: Nat)
             listType = (error "List type" :: [Nat])

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

type Prop a = a

infix 0 =:=

(=:=) :: a -> a -> Prop a
(=:=) = (=:=)

proveBool :: Bool -> Prop Bool
proveBool = (=:= True)

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

-- Boolean functions

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- Natural numbers

Z     == Z     = True
(S x) == (S y) = x == y
_     == _     = False

Z     <= _     = True
(S x) <= (S y) = x <= y
_     <= _     = False

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

-- List functions

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _    -> count x ys

prop_52 :: Nat -> [Nat] -> Prop Nat
prop_52 n xs = (count n xs =:= count n (rev xs))

