{-# LANGUAGE DeriveDataTypeable #-}
module Iterate where

import Prelude (fmap,undefined,error,Eq,Ord)

import Data.Typeable
import HipSpec.Prelude
import Test.QuickSpec.Signature hiding (total)

data List = A ::: List | Nil
  deriving (Eq,Ord,Typeable)

id :: A -> A
id x = x

ind :: List -> List
ind Nil      = Nil
ind (x:::xs) = x ::: ind xs

(x:::xs) ++ ys = x:::(xs ++ ys)
Nil      ++ ys = ys

map f Nil      = Nil
map f (x:::xs) = f x ::: map f xs

head (x:::xs) = x
tail (x:::xs) = xs

repeat x = x:::repeat x
iterate f x = x:::iterate f (f x)

cycle xs@(_:::_) = xs ++ cycle xs

sig = signature
    [ pvars ["x","y","z"]    (undefined :: A)
    , pvars ["xs","ys","zs"] (undefined :: List)
    , vars1 ["f","g"]        (undefined :: A -> A)
    , blind0 "id" id
    , "Nil"     `fun0` Nil
    , ":::"     `fun2` (:::)
    , "ind"     `fun1` ind
    , "++"      `fun2` (++)
    , "iterate" `fun2` iterate
    , "repeat"  `fun1` repeat
    , "map"     `fun2` map
    , "cycle"   `fun1` cycle
    , "head"    `fun1` head
    , "tail"    `fun1` tail
--    , withQuickCheckSize 10
    ]

prop_huh :: A -> (A -> A) -> (A -> A) -> Prop List
prop_huh x f g = total x ==> total f ==> total g ==> iterate f x =:= iterate g x

prop_duh :: A -> A -> (A -> A) -> Prop List
prop_duh x y f = total x ==> total y ==> total f ==> iterate f x =:= iterate f y

instance Arbitrary List where
    arbitrary = toList `fmap` arbitrary

instance Partial List where
    unlifted xs = toList `fmap` unlifted (fromList xs)

fromList :: List -> [A]
fromList (x ::: xs) = x : fromList xs
fromList Nil        = []

toList :: [A] -> List
toList (x:xs) = x ::: toList xs
toList []     = Nil

