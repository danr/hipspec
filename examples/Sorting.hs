module Sorting where

import Prelude (Bool(..),undefined,Ordering(..))
import HipSpec
import Nat
import Test.QuickSpec.Signature

{-
prop_T14 :: [Nat] -> Prop Bool
prop_T14 x = proveBool (sorted (isort x))
-}

(<=) :: Nat -> Nat -> Bool
x <= y = case x `cmp` y of
    GT -> False
    _  -> True

cmp :: Nat -> Nat -> Ordering
Z   `cmp` Z   = EQ
Z   `cmp` S x = LT
S y `cmp` Z   = GT
S x `cmp` S y = x `cmp` y

swap :: Ordering -> Ordering
swap EQ = EQ
swap LT = GT
swap GT = LT

eq :: Nat -> Nat -> Bool
Z   `eq` Z   = True
S x `eq` S y = x `eq` y
_   `eq` _   = False

merge (x:xs) (y:ys)
    | x <= y = x:merge xs (y:ys)
    | True   = y:merge (x:xs) ys
merge xs [] = xs
merge [] ys = ys

mergesort []  = []
mergesort [x] = [x]
mergesort xs  = merge (mergesort (evens xs)) (mergesort (odds xs))

evens (x:_:xs) = x:evens xs
evens [x]      = [x]
evens []       = []

odds (_:y:ys) = y:odds ys
odds _        = []

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

isort' :: [Nat] -> [Nat] -> [Nat]
isort' []     ys = ys
isort' (x:xs) ys = isort' xs (insert x ys)

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

iff :: Bool -> [Nat] -> [Nat] -> [Nat]
iff True  xs _ = xs
iff False _ ys = ys

-- prop_sorted_tail a as = sorted (a:as) =:= True ==> sorted as =:= True

{-
prop1 x xs = sorted (iff (sorted xs) (insert x xs) []) =:= True
prop2 x xs = sorted (insert x (iff (sorted xs) xs [])) =:= True
prop3 x xs = sorted (insert x xs) =:= sorted xs
prop4 x xs = sorted (isort xs) =:= True
-}

--prop_length_insert x xs = length (insert x xs) =:= S (length xs)
--prop_length_isort  xs = length (isort xs) =:= length xs


length :: [Nat] -> Nat
length []     = Z
length (_:xs) = S (length xs)

{-
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
    -}
