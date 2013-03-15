{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}
module Main where
import Prelude (Ord)
import Prelude
       ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**), (>>=),
        (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
        error, id, return, not, fst, snd, map, filter, concat, concatMap,
        reverse, zip, null, takeWhile, dropWhile, all, any, Integer,
        negate, abs, divMod, String, Bool(True, False),
        Maybe(Nothing, Just))
import qualified Prelude
import HipSpec
import HipSpec.Prelude
import Data.Typeable
import Test.Feat

deriveEnumerable ''A

data Nat = Zero_nat
         | Suc Nat
         deriving (Eq, Ord, Typeable)

deriveEnumerable ''Nat

instance Arbitrary Nat where
        arbitrary = sized uniform

data Tree a = Leaf a
            | Node (Tree a) (Tree a)
            deriving (Eq, Ord, Typeable)

deriveEnumerable ''Tree

instance (Enumerable a) => Arbitrary (Tree a) where
        arbitrary = sized uniform

plusnat :: Nat -> Nat -> Nat
plusnat (Suc m) n = plusnat m (Suc n)
plusnat Zero_nat n = n

one_nat :: Nat
one_nat = Suc Zero_nat

size :: forall a . Tree a -> Nat
size (Leaf x) = one_nat
size (Node l r) = plusnat (size l) (size r)

tmap :: forall a b . (a -> b) -> Tree a -> Tree b
tmap f (Leaf x) = Leaf (f x)
tmap f (Node l r) = Node (tmap f l) (tmap f r)

unit :: forall a . a -> Tree a
unit x = Leaf x

append :: forall a . Tree a -> Tree a -> Tree a
append t1 t2 = Node t1 t2

mirror :: forall a . Tree a -> Tree a
mirror (Leaf x) = Leaf x
mirror (Node l r) = Node (mirror r) (mirror l)
main
  = hipSpec $( fileName )
      [vars ["a", "b", "c"] (Prelude.undefined :: Tree A),
       vars ["a", "b", "c"] (Prelude.undefined :: A),
       vars ["a", "b", "c"] (Prelude.undefined :: Nat),
       vars ["a", "b", "c"] (Prelude.undefined :: (A -> A)),
       fun1 "Leaf" (Leaf :: A -> Tree A),
       fun2 "Node" (Node :: (Tree A) -> (Tree A) -> Tree A),
       fun1 "Suc" (Suc :: Nat -> Nat), fun0 "Zero_nat" (Zero_nat :: Nat),
       fun2 "append" (append :: Tree A -> Tree A -> Tree A),
       fun1 "mirror" (mirror :: Tree A -> Tree A),
       fun0 "one_nat" (one_nat :: Nat),
       fun2 "plusnat" (plusnat :: Nat -> Nat -> Nat),
       fun1 "size" (size :: Tree A -> Nat),
       fun2 "tmap" (tmap :: (A -> A) -> Tree A -> Tree A),
       fun1 "unit" (unit :: A -> Tree A)]
