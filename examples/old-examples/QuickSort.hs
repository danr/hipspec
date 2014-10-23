{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module QuickSort where

import Prelude(Bool(..),undefined,return,Eq,Ord)
import HipSpec.Prelude
import Definitions
import QuickSpec.Signature
import Test.QuickCheck.All

{-# NOINLINE whenSorted #-}
whenSorted :: NList -> NList
whenSorted xs = if sorted xs then xs else NNil

filter :: (Nat -> Bool) -> NList -> NList
filter p (NCons x xs) | p x = NCons x (filter p xs)
                      | otherwise = filter p xs
filter p NNil = NNil

{-# NOINLINE lesser #-}
lesser :: Nat -> NList -> NList
lesser x xs = filter (<= x) xs

{-# NOINLINE greater #-}
greater :: Nat -> NList -> NList
greater x xs = filter (x <=) xs

qsort :: NList -> NList
qsort NNil = NNil
qsort (NCons x xs) = qsort (lesser x xs) +++ NCons x (qsort (greater x xs))

prop_qsort xs = sorted (qsort xs) =:= True
prop_qsort_when xs = whenSorted (qsort xs) =:= qsort xs
prop_lesser_when x xs = sorted (lesser x (whenSorted xs)) =:=  True
prop_greater_when x xs = sorted (greater x (whenSorted xs)) =:=  True

-- Alternative definition of sorted


allLesser :: Nat -> NList -> Bool
allLesser x NNil = True
allLesser x (NCons y ys) = if x <= y then allLesser x ys else False

sorted' :: NList -> Bool
sorted' NNil = True
sorted' (NCons x xs) = if allLesser x xs then sorted' xs else False

prop_sorteds xs = sorted' xs =:= sorted xs

{-# NOINLINE whenSorted' #-}
whenSorted' :: NList -> NList
whenSorted' xs = if sorted' xs then xs else NNil

prop_qsort2 xs = sorted' (qsort xs) =:= True
prop_qsort_when2 xs = whenSorted' (qsort xs) =:= qsort xs
prop_lesser_when2 x xs = sorted' (lesser x (whenSorted' xs)) =:=  True
prop_greater_when2 x xs = sorted' (greater x (whenSorted' xs)) =:=  True

{-
prop_elem_qsort x xs = elem x xs =:= elem x (qsort xs)
prop_count_qsort x xs = count x xs =:= count x (qsort xs)
-}

prop_help n xs = nlength xs =:= n ==> sorted' (qsort xs) =:= True

prop_help2 n xs = nlength xs =:= n ==> nlength (qsort xs) =:= n

prop_help3 x xs = nlength (lesser x xs) <= nlength xs =:= True
prop_help4 x xs = nlength (greater x xs) <= nlength xs =:= True

main = $(quickCheckAll)

