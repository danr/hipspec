{-# LANGUAGE DeriveDataTypeable #-}
module Iterate where

import Prelude (fmap,undefined,error,Eq,Ord)

import Data.Typeable
import HipSpec.Prelude

data List = A ::: List | Nil
  deriving (Eq,Ord,Typeable)

id :: A -> A
id x = x

(x:::xs) ++ ys = x:::(xs ++ ys)
Nil      ++ ys = ys

map f Nil      = Nil
map f (x:::xs) = f x ::: map f xs

head (x:::xs) = x
tail (x:::xs) = xs

repeat x = x:::repeat x
iterate f x = x:::iterate f (f x)

cycle Nil = error "cycle: empty list"
cycle xs  = xs' where xs' = xs ++ xs'

cycle' xs = xs ++ cycle' xs

sig = signature
    [ pvars ["x","y","z"]    (undefined :: A)
    , pvars ["xs","ys","zs"] (undefined :: List)
    , vars ["f","g"]         (undefined :: A -> A)
    , blind0 "id" id
    , "Nil"     `fun0` Nil
    , ":::"     `fun2` (:::)
    , "++"      `fun2` (++)
    , "iterate" `fun2` iterate
    , "repeat"  `fun1` repeat
    , "cycle"   `fun1` cycle
    , "head"    `fun1` head
    , "tail"    `fun1` tail
    , "map"     `fun2` map
--    , withQuickCheckSize 10
    ]

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

