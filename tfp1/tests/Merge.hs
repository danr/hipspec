module Merge where

import Prelude hiding ((.))

-- Apparently this gives rise to lets which bind the same name
-- That's really ugly.

f . g = \x -> f (g x)

isGT GT = True
isGT _  = False

isn'tGT GT = False
isn'tGT _  = True

sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp = mergeAll . sequences
  where
    sequences (a:b:xs)
      | isGT (a `cmp` b) = descending b [a]  xs
      | True             = ascending  b (a:) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | isGT (a `cmp` b) = descending b (a:as) bs
    descending a as bs   = (a:as): sequences bs

    ascending a as (b:bs)
      | isn'tGT (a `cmp` b) = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs       = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge as@(a:as') bs@(b:bs')
      | isGT (a `cmp` b) = b:merge as  bs'
      | True             = a:merge as' bs
    merge [] bs          = bs
    merge as []          = as
