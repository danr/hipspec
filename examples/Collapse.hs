module Collapse where

import HipSpec

-- Double speed so normal induction cannot catch it
dmap :: (a -> b) -> [a] -> [b]
dmap f (x:y:zs) = f x:f y:dmap f zs
dmap f [x]      = [f x]
dmap _ []       = []

three :: Int -> Int
three _ = 3

tre :: Int -> Int
tre _ = 3

-- These are all to be proved without induction by making the closures equal
prop_collapse1 :: [Int] -> Prop [Int]
prop_collapse1 xs = dmap (\ _ -> 3) xs =:= dmap three xs

prop_collapse2 :: [Int] -> Prop [Int]
prop_collapse2 xs = dmap (\ _ -> 3) xs =:= dmap tre xs

idd :: a -> a
idd x = x

prop_collapse3 :: [a] -> Prop [a]
prop_collapse3 xs = dmap (\ u -> u) xs =:= dmap idd xs

