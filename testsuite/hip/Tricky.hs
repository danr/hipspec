-- Lists and functions, many properties come from QuickSpec
module ListFunctions where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),Int)

data Nat = Z | S Nat

-- PAPs

Z     + y = y
(S x) + y = S (x + y)

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

one = S Z

-- (+ one) and (one +) is not equal here. (of course) One is a finite
-- theorem and the other is a theorem. The two-depth structural
-- induction finds the finite theorem, but the simple induction fails
-- to find this as it is not a theorem with : if the natural number is
-- not total.
incr = map (one +)

incrrec (x:xs) = S x : incrrec xs
incrrec []     = []

prop_equal :: [Nat] -> Prop [Nat]
prop_equal xs = incrrec xs =:= incr xs

-- double speed fpi -----------------------------------------------------------

iter :: (a -> a) -> a -> [a]
iter f x = x : iter f (f x)

doublemap :: (a -> b) -> [a] -> [b]
doublemap f [] = []
doublemap f [x] = [f x]
doublemap f (x:y:zs) = f x:f y:doublemap f zs

prop_doublemap_iter :: (a -> a) -> a -> Prop [a]
prop_doublemap_iter f x = doublemap f (iter f x) =:= iter f (f x)

doublemap' :: (a -> b) -> [a] -> [b]
doublemap' f [] = []
doublemap' f (x:xs) = f x : case xs of
                               []   -> []
                               y:zs -> f y : doublemap' f zs

prop_doublemap'_iter :: (a -> a) -> a -> Prop [a]
prop_doublemap'_iter f x = doublemap' f (iter f x) =:= iter f (f x)

-- This needs depth 2 on structural induction
-- Is it possible to prove this with take lemma? Maybe it's time to upvote take lemma.
prop_doublemaps :: Prop ((a -> b) -> [a] -> [b])
prop_doublemaps = doublemap =:= doublemap'

finite :: [a] -> Bool
finite [] = True
finite (x:xs) = finite xs

prop_all_lists_finite :: [a] -> Prop Bool
prop_all_lists_finite xs = finite xs =:= True

-- Nub idempotency, which is true for total but not partial lists -------------

otherwise = True

True  == True  = True
False == False = True
_     == _     = False

nub :: [Bool] -> [Bool]
nub (True :True :xs) = nub (True:xs)
nub (False:False:xs) = nub (False:xs)
nub (x:xs)           = x:nub xs
nub _                = []

nub' :: [Bool] -> [Bool]
nub' (x:y:xs) | x == y    = nub' (y:xs)
              | otherwise = x:nub' (y:xs)
nub' xs                   = xs

prop_nub_idem :: [Bool] -> Prop [Bool]
prop_nub_idem xs = nub (nub xs) =:= nub xs

prop_nub'_idem :: [Bool] -> Prop [Bool]
prop_nub'_idem xs = nub' (nub' xs) =:= nub' xs

prop_nub_equal :: Prop ([Bool] -> [Bool])
prop_nub_equal = nub =:= nub'
