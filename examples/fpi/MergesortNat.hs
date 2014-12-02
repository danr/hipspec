{-# LANGUAGE DeriveDataTypeable #-}
module MergesortNat(module MergesortNat,module Nat) where

import Prelude (Bool(..),undefined,Ordering(..), (&&), (||), otherwise, not, fmap, Eq(..), Ord, fst, snd)
import HipSpec hiding ((===))
import Nat (Nat(..))
import List ((++))
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

-- app (x,y) = x ++ y

uncurry f (x,y) = f x y

prop_atotal a b = a <= b || b <= a =:= True

prop_merge_ord xs ys = ord xs =:= True ==> ord ys =:= True ==> ord (merge xs ys) =:= True

prop_cancel xs ys = msort xs =:= msort ys ==> xs =:= ys


(===),(=/=) :: [Nat] -> [Nat] -> Bool
[]     === []     = True
(x:xs) === (y:ys) = x == y && xs === ys
_      === _      = False

xs =/= ys = not (xs === ys)

prop_cancel2 xs ys zs = True =:=
        msort xs =/= zs || msort ys =/= zs
     || msort xs === xs || msort ys === ys
     || xs === ys

{-
prop_msort_ord xs = ord (msort xs) =:= True

prop_msort_permutation xs x = count x xs =:= count x (msort xs)

prop_count_split x xs = count x (uncurry (++) (split xs)) =:= count x xs
-}
