{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Main where

import HipSpec
import HipSpec.Prelude

import Data.Typeable
import Control.Applicative
import Prelude (undefined,Eq,Show,Ord,return,div,sqrt,round,($),(!!),iterate,fromInteger,toInteger,Double)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []         = []

head :: [Nat] -> Nat
head (x:xs) = x
head _ = Z

tail :: [a] -> [a]
tail (x:xs) = xs
tail _ = []

prop_revrev :: [a] -> [a] -> Prop ([a])
prop_revrev xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_revinv :: [a] -> Prop ([a])
prop_revinv xs = reverse (reverse xs) =:= xs

data Fun a = NilS | Unit a | Append (Fun a) (Fun a)
  deriving (Eq, Ord, Typeable, Show)

(+++) :: Fun a -> Fun a -> Fun a
{-
NilS +++ x = x
x +++ NilS = x
-}
x +++ y = x `Append` y

prop_app :: Fun a -> Fun a -> Prop [a]
prop_app x y = toList x ++ toList y =:= toList (x +++ y)

prop_nil :: Prop [a]
prop_nil = toList NilS =:= []

reverseS :: Fun a -> Fun a
reverseS NilS = NilS
reverseS (Unit x) = Unit x
reverseS (Append x y) = Append (reverseS y) (reverseS x)

prop_reverse :: Fun a -> Prop ([a])
prop_reverse x = toList (reverseS x) =:= reverse (toList x)

toList :: Fun a -> [a]
toList NilS = []
toList (Unit x) = [x]
toList (Append x y) = toList x ++ toList y

eval :: Fun a -> [a] -> [a]
eval NilS xs = xs
eval (Unit x) xs = x:xs
eval (Append xs ys) zs = eval xs (eval ys zs)

toList' :: Fun a -> [a]
toList' s = eval s []

headS :: Fun Nat -> Nat
headS (Unit x) = x
headS (Append x y) = headS x
headS _ = Z

tailS :: Fun a -> Fun a
tailS (Unit x) = NilS
tailS (Append x y) = tailS x +++ y
tailS _ = NilS

prop_toLists :: Fun a -> Prop [a]
prop_toLists s = toList s =:= toList' s

prop_head :: Fun Nat -> Prop Nat
prop_head xs = headS xs =:= head (toList xs)

prop_tail :: Fun a -> Prop [a]
prop_tail xs = toList (tailS xs) =:= tail (toList xs)

type Seq = Fun Nat

type List = [Nat]

main = hipSpec $(fileName)
    [ vars ["x","y","z"]    intType
    , vars ["s","t","u"]    seqType
    , vars ["xs","ys","zs"] listType
    , fun0 "Z"        Z
    , fun0 "[]"       ([]      :: List)
    , fun2 ":"        ((:)     :: Nat -> List -> List)
    , fun2 "++"       ((++)     :: List -> List -> List)
    , fun1 "reverse"  (reverse  :: List -> List)
    , fun2 "+++"      ((+++) :: Seq -> Seq -> Seq)
    , fun1 "reverseS" (reverseS :: Seq -> Seq)
    , fun1 "Unit"     (Unit :: Nat -> Seq)
    , fun1 "toList"   (toList :: Seq -> List)
    , fun1 "toList'"  (toList' :: Seq -> List)
    , fun2 "eval"     (eval :: Seq -> List -> List)
    , fun1 "head"     (head :: List -> Nat)
    , fun1 "tail"     (tail :: List -> List)
    , fun1 "headS"    (headS :: Seq -> Nat)
    , fun1 "tailS"    (tailS :: Seq -> Seq)
    ]
  where
    intType  = undefined :: Nat
    listType = undefined :: List
    seqType  = undefined :: Seq

instance Arbitrary a => Arbitrary (Fun a) where
  arbitrary = sized arbFun
    where
      arbFun s = frequency
        [ (1, return NilS)
        , (1, Unit <$> arbitrary)
        , (s, (+++) <$> arbFun (s `div` 2) <*> arbFun (s `div` 2))
        ]

data Nat = Z | S Nat deriving (Eq, Ord, Typeable, Show)

instance Arbitrary Nat where
  arbitrary = sized $ \s -> (iterate S Z !!) <$> choose (0, round (sqrt (fromInteger (toInteger s)) :: Double))

