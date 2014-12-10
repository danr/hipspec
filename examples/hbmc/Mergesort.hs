{-# LANGUAGE DeriveDataTypeable #-}
module Mergesort(module Mergesort,module Nat) where

import Prelude (Bool(..),undefined,Ordering(..), (&&), (||), otherwise, not, fmap, Eq(..), Ord, fst, snd)
import HipSpec hiding ((===))
import Nat (Nat(..),(+),(*))
import List (length)
import Test.QuickCheck hiding ((==>),(===))
import GHC.Types
import Data.Typeable

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
S _ <= Z   = False
S x <= S y = x <= y

count :: Nat -> [Nat] -> Nat
count n [] = Z
count n (x:xs)
  | n <= x && x <= n = S (count n xs)
  | otherwise = count n xs

msort :: [Nat] -> [Nat]
msort []  = []
msort [x] = [x]
msort xs  = merge (msort (evens xs)) (msort (odds xs))

evens :: [a] -> [a]
evens [] = []
evens [x] = [x]
evens (x:_:xs) = x:evens xs

odds :: [a] -> [a]
odds [] = []
odds [_] = []
odds (_:y:xs) = y:odds xs

merge :: [Nat] -> [Nat] -> [Nat]
merge (x:xs) (y:ys)
    | x <= y    = x:merge xs (y:ys)
    | otherwise = y:merge (x:xs) ys
merge xs [] = xs
merge [] ys = ys

ord :: [Nat] -> Bool
ord (x:y:xs) = if x <= y then ord (y:xs) else False
ord _        = True

prop_atotal     a b = a <= b =:= True \/ b <= a =:= True
prop_atotal_not a b = a <= b =:= True /\ b <= a =:= True ==> True =:= False

-- prop_merge_ord      xs ys = ord xs =:= True  ==> ord ys =:= True  ==> ord (merge xs ys) =:= True
prop_merge_ord_not1 xs ys = ord xs =:= True  ==> ord ys =:= True  ==> ord (merge xs ys) =:= False
prop_merge_ord_not2 xs ys = ord xs =:= False ==> ord ys =:= True  ==> ord (merge xs ys) =:= True
prop_merge_ord_not3 xs ys = ord xs =:= True  ==> ord ys =:= False ==> ord (merge xs ys) =:= True

prop_cancel xs ys = msort xs =:= msort ys ==> xs =:= ys

n2  () = S (S Z)
n3  () = S (n2 ())
n4  () = S (n3 ())
n5  () = S (n4 ())
n6  () = S (n5 ())
n7  () = S (n6 ())
n8  () = S (n7 ())
n9  () = S (n8 ())
n10 () = S (n9 ())

prop_cancel2 xs ys zs =
        msort xs =:= zs
     /\ msort ys =:= zs
     /\ False =:= length xs <= n10 ()
    ==> msort xs =:= xs
     \/ msort ys =:= ys
     \/ xs =:= ys

prop_msort_ord_not xs = ord (msort xs) =:= False

prop_msort_permutation_wrong1 xs x = count x xs <= n10 () =:= False ==> count x xs =:= count (S x) (msort xs)
prop_msort_permutation_wrong2 xs x = count x xs <= n10 () =:= False ==> count (S x) xs =:= count x (msort xs)

