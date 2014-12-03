module SelectionSort where

import Prelude hiding ((++),minimum,length)
import HipSpec
import List ((++))
import Test.QuickCheck hiding ((==>))
import GHC.Types
import Data.Typeable
import Sorting

delete :: Integer -> [Integer] -> [Integer]
delete x (y:ys)
    | x == y    = ys
    | otherwise = y:delete x ys
delete _ [] = []

minimum :: Integer -> [Integer] -> Integer
minimum a []     = a
minimum a (x:xs)
    | x < a     = minimum x xs
    | otherwise = minimum a xs

ssort :: [Integer] -> [Integer]
ssort []     = []
ssort (x:xs) = let m = minimum x xs in m : ssort (delete m (x:xs))

prop_ssort_sorted xs = sorted (ssort xs) =:= True

-- prop_ssort_count n xs = count n xs =:= count n (ssort xs)

prop_ssort_length xs = length xs =:= length (ssort xs)

