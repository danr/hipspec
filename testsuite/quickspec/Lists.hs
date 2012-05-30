{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return,div)
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

type List = ListP Int

prop_revrev :: ListP a -> ListP a -> Prop (ListP a)
prop_revrev xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_revinv :: ListP a -> Prop (ListP a)
prop_revinv xs = reverse (reverse xs) =:= xs

data SeqP a = NilS | NonNilS (NonNilSeqP a) deriving (Eq, Ord, Typeable)

(+++) :: SeqP a -> SeqP a -> SeqP a
NilS +++ x = x
x +++ NilS = x
NonNilS x +++ NonNilS y = NonNilS (x `Append` y)

prop_app :: SeqP a -> SeqP a -> Prop (ListP a)
prop_app x y = toList x ++ toList y =:= toList (x +++ y)

pointS :: a -> SeqP a
pointS x = NonNilS (Unit x)

prop_point :: a -> Prop (ListP a)
prop_point x = toList (pointS x) =:= point x

reverseS :: SeqP a -> SeqP a
reverseS NilS = NilS
reverseS (NonNilS x) = NonNilS (reverseSS x)

prop_reverse :: SeqP a -> Prop (ListP a)
prop_reverse x = toList (reverseS x) =:= reverse (toList x)

toList :: SeqP a -> ListP a
toList NilS = Nil
toList (NonNilS x) = toListS x

data NonNilSeqP a = Unit a | Append (NonNilSeqP a) (NonNilSeqP a) deriving (Eq, Ord, Typeable)

prop_unit :: a -> Prop (ListP a)
prop_unit x = toListS (Unit x) =:= point x

prop_appS :: NonNilSeqP a -> NonNilSeqP a -> Prop (ListP a)
prop_appS x y = toListS (x `Append` y) =:= toListS x ++ toListS y

reverseSS (Unit x) = Unit x
reverseSS (Append x y) = Append (reverseSS y) (reverseSS x)

prop_reverseSS :: NonNilSeqP a -> Prop (ListP a)
prop_reverseSS x = toListS (reverseSS x) =:= reverse (toListS x)

toListS :: NonNilSeqP a -> ListP a
toListS (Unit x) = point x
toListS (Append x y) = toListS x ++ toListS y

type Seq = SeqP Int
type NonNilSeq = NonNilSeqP Int

main = hipSpec "Lists.hs" conf 3
  where conf = describe "Lists"
                [ var "x"        intType
                , var "y"        intType
                , var "z"        intType
                , var "xs"       seqType
                , var "ys"       seqType
                , var "zs"       seqType
                , var "xs"       seqSType
                , var "ys"       seqSType
                , var "zs"       seqSType
                , var "xs"       listType
                , var "ys"       listType
                , var "zs"       listType
                , con "Nil"      (Nil      :: List)
                , con "Cons"     (Cons     :: Int -> List -> List)
                , con "point"    (point    :: Int -> List)
                , con "++"       ((++)     :: List -> List -> List)
                , con "reverse"  (reverse  :: List -> List)
                , con "+++"      ((+++) :: Seq -> Seq -> Seq)
                , con "pointS"   (pointS :: Int -> Seq)
                , con "reverseS" (reverseS :: Seq -> Seq)
                , con "Unit"     (Unit :: Int -> NonNilSeq)
                , con "Append"   (Append :: NonNilSeq -> NonNilSeq -> NonNilSeq)
                , con "reverseSS" (reverseSS :: NonNilSeq -> NonNilSeq)
                , con "toList" (toList :: Seq -> List)
                , con "toListS" (toListS :: NonNilSeq -> List)
                ]
                   where
                     intType   = undefined :: Int
                     listType  = undefined :: List
                     seqType = undefined :: Seq
                     seqSType = undefined :: NonNilSeq

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
                            (s, NonNilS <$> arbitrary)]

instance Classify Seq where
  type Value Seq = Seq
  evaluate = return

instance Arbitrary NonNilSeq where
  arbitrary = sized arbSeqP
    where
      arbSeqP s = frequency [(1, Unit <$> arbitrary)
                           ,(s, Append <$> arbSeqP (s `div` 2) <*> arbSeqP (s `div` 2))]

instance Classify NonNilSeq where
  type Value NonNilSeq = NonNilSeq
  evaluate = return

-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
