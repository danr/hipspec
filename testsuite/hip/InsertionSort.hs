module InsertionSort where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..))

data Nat = Z | S Nat
  deriving (Eq,Ord,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,25)

-- Insertion sort for natural numbers -----------------------------------------

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

True  && a = a
False && _ = False

length :: [a] -> Nat
length [] = Z
length (_:xs) = S (length xs)

elem :: Nat -> [Nat] -> Bool
elem x (y:ys) =
  case x == y of
    True -> True
    False -> elem x ys
elem x [] = False

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    False -> count x ys

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insert x (sort xs)

prop_elem :: Nat -> [Nat] -> Prop Bool
prop_elem n xs = elem n xs =:= elem n (sort xs)

prop_elem_insert :: Nat -> [Nat] -> Prop Bool
prop_elem_insert x xs = proveBool (elem x (insert x xs))


prop_sort_idem :: [Nat] -> Prop [Nat]
prop_sort_idem xs = sort (sort xs) =:= sort xs

prop_length_sort :: [Nat] -> Prop Nat
prop_length_sort xs = length (sort xs) =:= length xs

prop_sort_sorts :: [Nat] -> Prop Bool
prop_sort_sorts xs = proveBool (sorted (sort xs))

prop_count :: Nat -> [Nat] -> Prop Nat
prop_count n xs = count n xs =:= count n (sort xs)

-- Insertion Sort for Booleans ------------------------------------------------

otherwise = True

(<.) :: Bool -> Bool -> Bool
False <. True = True
_     <. _    = False

(=.) :: Bool -> Bool -> Bool
True  =. True  = True
False =. False = True
_     =. _     = False

False || a = a
True  || _ = True

countBool :: Bool -> [Bool] -> Nat
countBool x [] = Z
countBool x (y:ys) =
  case x =. y of
    True  -> S (countBool x ys)
    False -> countBool x ys

elemBool :: Bool -> [Bool] -> Bool
elemBool x (y:ys) =
  case x =. y of
    True -> True
    False -> elemBool x ys
elemBool x [] = False

sortedBools :: [Bool] -> Bool
sortedBools [] = True
sortedBools [x] = True
sortedBools (x:y:ys) = ((x =. y) || (x <. y)) && sortedBools (y:ys)

insertBool :: Bool -> [Bool] -> [Bool]
insertBool n [] = [n]
insertBool n (x:xs) | n <. x    = n : x : xs
                | otherwise = x : insertBool n xs

sortBools :: [Bool] -> [Bool]
sortBools [] = []
sortBools (x:xs) = insertBool x (sortBools xs)

prop_sortBools_idem :: [Bool] -> Prop [Bool]
prop_sortBools_idem xs = sortBools (sortBools xs) =:= sortBools xs

prop_length_sortBools :: [Bool] -> Prop Nat
prop_length_sortBools xs
  = length (sortBools xs) =:= length xs

prop_sortBools_sorts :: [Bool] -> Prop Bool
prop_sortBools_sorts xs
  = sortedBools (sortBools xs) =:= True

prop_countBool :: Bool -> [Bool] -> Prop Nat
prop_countBool x xs
  = countBool x xs =:= countBool x (sortBools xs)

prop_elemBool :: Bool -> [Bool] -> Prop Bool
prop_elemBool n xs = elemBool n xs =:= elemBool n (sortBools xs)

prop_elemBool_insert :: Bool -> [Bool] -> Prop Bool
prop_elemBool_insert x xs = proveBool (elemBool x (insertBool x xs))

-- Tests ----------------------------------------------------------------------

main = do
  quickCheck (printTestCase "prop_length_sort" (prop_length_sort :: [Nat] -> Prop Nat))
  quickCheck (printTestCase "prop_sort_sorts" (prop_sort_sorts :: [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_count" (prop_count :: Nat -> [Nat] -> Prop Nat))
  quickCheck (printTestCase "prop_elem" (prop_elem :: Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_elem_insert" (prop_elem_insert :: Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_length_sortBools" (prop_length_sortBools :: [Bool] -> Prop Nat))
  quickCheck (printTestCase "prop_sortBools_sorts" (prop_sortBools_sorts :: [Bool] -> Prop Bool))
  quickCheck (printTestCase "prop_countBool" (prop_countBool :: Bool -> [Bool] -> Prop Nat))
  quickCheck (printTestCase "prop_elemBool" (prop_elemBool :: Bool -> [Bool] -> Prop Bool))
  quickCheck (printTestCase "prop_elemBool_insert" (prop_elemBool_insert :: Bool -> [Bool] -> Prop Bool))
