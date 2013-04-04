{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module QuickSort where

import Prelude(Bool(..),undefined,return,Eq,Ord)
import HipSpec.Prelude
import Definitions
import Test.QuickSpec.Signature
import Test.QuickCheck.All

-- Koen Style:
{-# NOINLINE whenSorted #-}
whenSorted :: NList -> NList
whenSorted xs = if sorted xs then xs else NNil

greater :: Nat -> NList -> NList
greater x NNil         = NNil
greater x (NCons y ys) = if x <= y then NCons y (greater x ys) else greater x ys

lesser :: Nat -> NList -> NList
lesser x NNil         = NNil
lesser x (NCons y ys) = if x <= y then lesser x ys else NCons y (lesser x ys)

qsort :: NList -> NList
qsort NNil = NNil
qsort (NCons x xs) = qsort (lesser x xs) +++ NCons x (qsort (greater x xs))

prop_qsort xs = sorted (qsort xs) =:= True
prop_qsort_when xs = whenSorted (qsort xs) =:= qsort xs
prop_lesser_when x xs = sorted (lesser x (whenSorted xs)) =:=  True
prop_greater_when x xs = sorted (greater x (whenSorted xs)) =:=  True

{-
prop_elem_qsort x xs = elem x xs =:= elem x (qsort xs)
prop_count_qsort x xs = count x xs =:= count x (qsort xs)
-}

main = $(quickCheckAll)

