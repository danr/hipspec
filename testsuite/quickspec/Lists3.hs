{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Main where

import Prelude (undefined,Eq,Show,Ord,return,div)
import qualified Prelude as P

import Data.Typeable

import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Control.Applicative

data ListP a = Cons a (ListP a) | Nil
  deriving (Show,Eq,Ord,Typeable)

(++) :: ListP a -> ListP a -> ListP a
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

point :: a -> ListP a
point x = Cons x Nil

reverse :: ListP a -> ListP a
reverse (Cons x xs) = reverse xs ++ point x
reverse Nil         = Nil

head :: ListP Nat -> Nat
head (Cons x xs) = x
head _ = Z

tail :: ListP a -> ListP a
tail (Cons x xs) = xs
tail _ = Nil

type List = ListP Nat

prop_revrev :: ListP a -> ListP a -> Prop (ListP a)
prop_revrev xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_revinv :: ListP a -> Prop (ListP a)
prop_revinv xs = reverse (reverse xs) =:= xs

data SeqP a = NilS | Unit a | Append (SeqP a) (SeqP a) deriving (Eq, Ord, Typeable, Show)

(+++) :: SeqP a -> SeqP a -> SeqP a
NilS +++ x = x
x +++ NilS = x
x +++ y = x `Append` y

prop_app :: SeqP a -> SeqP a -> Prop (ListP a)
prop_app x y = toList x ++ toList y =:= toList (x +++ y)

prop_nil :: Prop (ListP a)
prop_nil = toList NilS =:= Nil

prop_point :: a -> Prop (ListP a)
prop_point x = toList (Unit x) =:= point x

reverseS :: SeqP a -> SeqP a
reverseS NilS = NilS
reverseS (Unit x) = Unit x
reverseS (Append x y) = Append (reverseS y) (reverseS x)

prop_reverse :: SeqP a -> Prop (ListP a)
prop_reverse x = toList (reverseS x) =:= reverse (toList x)

toList :: SeqP a -> ListP a
toList NilS = Nil
toList (Unit x) = point x
toList (Append x y) = toList x ++ toList y

headS :: SeqP Nat -> Nat
headS (Unit x) = x
headS (Append x y) = headS x
headS _ = Z

tailS :: SeqP a -> SeqP a
tailS (Unit x) = NilS
tailS (Append x y) = tailS x +++ y
tailS _ = NilS

prop_head :: SeqP Nat -> Prop Nat
prop_head xs = headS xs =:= head (toList xs)

prop_tail :: SeqP a -> Prop (ListP a)
prop_tail xs = toList (tailS xs) =:= tail (toList xs)

type Seq = SeqP Nat

main = hipSpec "Lists3.hs" conf 3
  where conf = describe "Lists"
                [ var "x"        intType
                , var "y"        intType
                , var "z"        intType
                , var "xs"       seqType
                , var "ys"       seqType
                , var "zs"       seqType
                , var "xs"       listType
                , var "ys"       listType
                , var "zs"       listType
                , con "Nil"      (Nil      :: List)
                , con "Cons"     (Cons     :: Nat -> List -> List)
                , con "point"    (point    :: Nat -> List)
                , con "++"       ((++)     :: List -> List -> List)
                , con "reverse"  (reverse  :: List -> List)
                , con "+++"      ((+++) :: Seq -> Seq -> Seq)
                , con "reverseS" (reverseS :: Seq -> Seq)
                , con "Unit"     (Unit :: Nat -> Seq)
                , con "toList" (toList :: Seq -> List)
                , con "head" (head :: List -> Nat)
                , con "tail" (tail :: List -> List)
                , con "headS" (headS :: Seq -> Nat)
                , con "tailS" (tailS :: Seq -> Seq)
                , con "Z" Z
                ]
                   where
                     intType   = undefined :: Nat
                     listType  = undefined :: List
                     seqType = undefined :: Seq

instance Arbitrary List where
  arbitrary = sized arbList
    where
      arbList s = frequency [(1,return Nil)
                            ,(s,Cons <$> arbitrary <*> arbList (s `div` 2))
                            ]

instance Classify List where
  type Value List = List
  evaluate = return

instance Arbitrary Seq where
  arbitrary = sized arbSeqP
    where
      arbSeqP s = frequency [(1, return NilS),
                             (1, Unit <$> arbitrary),
                             (s, (+++) <$> arbSeqP (s `div` 2) <*> arbSeqP (s `div` 2))]

instance Classify Seq where
  type Value Seq = Seq
  evaluate = return

-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a

data Nat = Z | S Nat deriving (Eq, Ord, Typeable, Show)
instance Arbitrary Nat where
  arbitrary = (P.iterate S Z P.!!) <$> choose (0, 10)

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return