module Sorting where

import Prelude (Bool(..),undefined)
import HipSpec
import Nat
import Test.QuickSpec.Signature

prop_T14 :: [Nat] -> Prop Bool
prop_T14 x = proveBool (sorted (isort x))

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
_   <= Z   = False
S x <= S y = x <= y

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

True && x = x
_    && _ = False

sorted :: [Nat] -> Bool
sorted (x:y:xs) = x <= y && sorted (y:xs)
sorted _        = True

-- Koen Style:
whenSorted :: [Nat] -> [Nat]
whenSorted xs = if sorted xs then xs else []

-- Use this, or the signature with depth 4 below (takes a lot of time)
prop_koen x xs = sorted (insert x (whenSorted xs)) =:= True

sig =
    [ fun0 "False"          ( False :: Bool )
    , fun0 "True"           ( True :: Bool )
    , fun2 ":"              ( (:) :: Nat -> [Nat] -> [Nat] )
    , fun0 "[]"             ( [] :: [Nat] )
    , fun0 "Z"              ( Z :: Nat )
    , fun1 "S"              ( S :: Nat -> Nat )
    , fun1 "whenSorted"     ( (whenSorted) :: [Nat] -> [Nat] )
    , fun1 "sorted"         ( (sorted) :: [Nat] -> Bool )
    , fun1 "isort"          ( (isort) :: [Nat] -> [Nat] )
    , fun2 "insert"         ( (insert) :: Nat -> [Nat] -> [Nat] )
    , fun2 "<="             ( (<=) :: Nat -> Nat -> Bool )
    , fun2 "&&"             ( (&&) :: Bool -> Bool -> Bool )
    , vars ["a","b","c"]    ( undefined :: Bool )
    , vars ["x","y","z"]    ( undefined :: Nat )
    , vars ["xs","ys","zs"] ( undefined :: [Nat] )
    , withTests 100
    , withQuickCheckSize 20
    , withSize 1000
    ]
