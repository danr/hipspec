{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module MergeSort where

import Prelude(Bool(..),undefined,return,Eq,Ord)
import HipSpec.Prelude
import Definitions
import QuickSpec.Signature
import Test.QuickCheck.All

-- Koen Style:
{-# NOINLINE whenSorted #-}
whenSorted :: NList -> NList
whenSorted xs = if sorted xs then xs else NNil

merge :: NList -> NList -> NList
merge (NCons x xs)    (NCons y ys)   =
    if x <= y
        then NCons x (merge xs (NCons y ys))
        else NCons y (merge (NCons x xs) ys)
merge xs@(NCons _ _)  NNil           = xs
merge NNil            ys@(NCons _ _) = ys
merge NNil            NNil           = NNil

data Pair = Pair !NList !NList deriving (Eq,Typeable,Ord)

instance Arbitrary Pair where
    arbitrary = do
        a <- arbitrary
        b <- arbitrary
        return (Pair a b)

evens :: NList -> NList
evens NNil = NNil
evens (NCons x NNil) = NNil
evens (NCons x (NCons y zs)) = NCons x (evens zs)

odds :: NList -> NList
odds NNil = NNil
odds (NCons x NNil) = NCons x NNil
odds (NCons x (NCons y zs)) = NCons y (odds zs)

interleave :: NList -> NList -> NList
interleave NNil         ys = ys
interleave (NCons x xs) ys = NCons x (interleave ys xs)

prop_interleave xs = interleave (evens xs) (odds xs) =:= xs

msort :: NList -> NList
msort NNil = NNil
msort (NCons x NNil) = NCons x NNil
msort xs@(NCons _ (NCons _ _)) = merge (msort (evens xs)) (msort (odds xs))

prop_msort xs = whenSorted (msort xs) =:= msort xs
prop_sorted xs = sorted (msort xs) =:= True

prop_merge xs ys = sorted (merge (whenSorted xs) (whenSorted ys)) =:= True

{-
prop_elem_msort x xs = elem x xs =:= elem x (msort xs)
prop_count_msort x xs = count x xs =:= count x (msort xs)
-}

main = $(quickCheckAll)

