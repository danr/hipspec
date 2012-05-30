module MergeSort where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..))

otherwise = True

data Ordering = LT | EQ | GT

cmp :: Bool -> Bool -> Ordering
cmp True  True  = EQ
cmp False False = EQ
cmp True  False = GT
cmp False True  = LT

(<.) :: Bool -> Bool -> Bool
False <. True = True
_     <. _    = False

(=.) :: Bool -> Bool -> Bool
True  =. True  = True
False =. False = True
_     =. _     = False

False || a = a
True  || _ = True

True  && a = a
False && _ = False

sorted :: [Bool] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = ((x =. y) || (x <. y)) && sorted (y:ys)

count :: Bool -> [Bool] -> Nat
count x [] = Z
count x (y:ys) =
  case x =. y of
    True  -> S (count x ys)
    False -> count x ys

elem :: Bool -> [Bool] -> Bool
elem x (y:ys) =
  case x =. y of
    True -> True
    False -> elem x ys
elem x [] = False

data Nat = Z | S Nat
  deriving (Eq,Ord,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,25)

length :: [a] -> Nat
length [] = Z
length (_:xs) = S (length xs)


(==) :: Ordering -> Ordering -> Bool
GT == GT = True
EQ == EQ = True
LT == LT = True
_  == _  = False

(/=) :: Ordering -> Ordering -> Bool
GT /= GT = False
EQ /= EQ = False
LT /= LT = False
_  /= _  = True

sort :: [Bool] -> [Bool]
sort xs = mergeAll (sequences xs)
  where
    sequences :: [Bool] -> [[Bool]]
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]

    descending :: Bool -> [Bool] -> [Bool] -> [[Bool]]
    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending :: Bool -> ([Bool] -> [Bool]) -> [Bool] -> [[Bool]]
    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = as [a]: sequences bs

    mergeAll :: [[Bool]] -> [Bool]
    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs :: [[Bool]] -> [[Bool]]
    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge :: [Bool] -> [Bool] -> [Bool]
    merge (a:as') (b:bs')
      | a `cmp` b == GT = b:merge (a:as') bs'
      | otherwise       = a:merge as'     (b:bs')
    merge [] bs         = bs
    merge as []         = as

prop_sort_idem :: [Bool] -> Prop [Bool]
prop_sort_idem xs = sort (sort xs) =:= sort xs

prop_length_sort :: [Bool] -> Prop Nat
prop_length_sort xs = length (sort xs) =:= length xs

prop_sort_sorts :: [Bool] -> Prop Bool
prop_sort_sorts xs = proveBool (sorted (sort xs))

prop_count :: Bool -> [Bool] -> Prop Nat
prop_count n xs = count n xs =:= count n (sort xs)

prop_elem :: Bool -> [Bool] -> Prop Bool
prop_elem n xs = elem n xs =:= elem n (sort xs)

main = do
  quickCheck (printTestCase "prop_sort_idem" (prop_sort_idem :: [Bool] -> Prop [Bool]))
  quickCheck (printTestCase "prop_length_sort" (prop_length_sort :: [Bool] -> Prop Nat))
  quickCheck (printTestCase "prop_sort_sorts" (prop_sort_sorts :: [Bool] -> Prop Bool))
  quickCheck (printTestCase "prop_count" (prop_count :: Bool -> [Bool] -> Prop Nat))
  quickCheck (printTestCase "prop_elem" (prop_elem :: Bool -> [Bool] -> Prop Bool))


