{-# LANGUAGE CPP,TemplateHaskell #-}
module HipSpec.Utils
    (
    -- * Convenience reexports
      module Control.Arrow
    , module Control.Applicative

    -- * Function composition
    , (.:)

    -- * Boolean inspection
    , (?)
    , ifM

    -- * Monadic concatenative combinators
    , concatMapM
    , concatFoldM

    -- * Cursored traversals of lists
    , selections
    , inspect
    , withPrevious
    , uniqueCartesian

    , replace
    , oper

    -- * Efficient nub and group
    , nubSorted
    , groupSortedOn
    , nubSortedOn
    , sortOn

    -- * Intersection
    , intersects

    -- * Pretty Show
    , ppShow

    -- * Allocation
    , allocate

    -- * Tests
    , tests

    ) where

import Control.Arrow       ((***),(&&&),first,second)
import Control.Applicative ((<$>),(<*>),Applicative)

import Control.Monad (liftM)

import Data.List
import Data.Function (on)
import Data.Ord      (comparing)

import Data.Char (isAlphaNum)

import Data.List
import Test.QuickCheck
import Test.QuickCheck.All

import qualified Text.Show.Pretty as Pretty

infixr 9 .:

-- | Function composition deluxe
--
--   @(f .: g) = \x y -> f (g x y)@
(.:) :: (b -> c) -> (a -> a' -> b) -> a -> a' -> c
(.:) = (.) . (.)

-- | Concatenate the results after mapM
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

-- | Folds and concats in a monad
concatFoldM :: Monad m => (a -> i -> m [a]) -> a -> [i] -> m [a]
concatFoldM _ a []     = return [a]
concatFoldM k a (x:xs) = do rs <- k a x
                            concatMapM (\r -> concatFoldM k r xs) rs

infixr 1 ?

-- | Apply the function if true, otherwise propagate
(?) :: Bool -> (a -> a) -> a -> a
True  ? f = f
False ? _ = id

-- | Monadic if
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb t f = do
    b <- mb
    if b then t else f

-- | Pair up a list with its previous and next elements
--
-- > selections "abc" = [("",'a',"bc"),("a",'b',"c"),("ab",'c',"")]
selections :: [a] -> [([a],a,[a])]
selections xs = map (fromSplit . (`splitAt` xs)) [0..length xs-1]
  where fromSplit (as,b:bs) = (as,b,bs)
        fromSplit _         = error "selections fromSplit unreachable"

-- | Pair up a list with the element and the rest of the elements
--
-- > inspect "abc" = [('a',"bc"),('b',"ac"),('c',"ab")]
inspect :: [a] -> [(a,[a])]
inspect = map (\(i,x,r) -> (x,i++r)) . selections

-- | Pair up a list with its previous elements
--
-- > withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

-- | Non-reflexive and non-symmetric cartesian product
--
-- > uniqueCartesian "abc" = [('a','b'),('a','c'),('b','c')]
uniqueCartesian :: [a] -> [(a,a)]
uniqueCartesian as = concat [ zip (repeat x) xs | (x:xs) <- tails as ]

sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn = sortBy . comparing

-- | /O(n log n)/ nub, but destroys ordering
nubSorted :: Ord a => [a] -> [a]
nubSorted = map head . group . sort

-- | /O(n log n)/ group, but destroys ordering
groupSortedOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortedOn f = groupBy ((==) `on` f)
                . sortBy (comparing f)

replace :: [a] -> Int -> a -> [a]
replace xs i x = case splitAt i xs of
    (l,_:r) -> l ++ [x] ++ r
    _       -> xs

-- | /O(n log n)/ nub by a comparison function. Destroys ordering
nubSortedOn :: Ord b => (a -> b) -> [a] -> [a]
nubSortedOn f = map head . groupSortedOn f

-- | Do these two lists have a non-empty intersection?
intersects :: Eq a => [a] -> [a] -> Bool
intersects = (not . null) .: intersect

-- | Pretty show
ppShow :: Show a => a -> String
ppShow = Pretty.ppShow

-- | Is this an operator?
oper :: String -> Bool
oper s | (l,'.':r) <- break (== '.') s, all isAlphaNum l = operSyms r
oper s = operSyms s

operSyms :: String -> Bool
operSyms s = not (null s') && all (`elem` opSyms) s'
  where s' = filter (`notElem` ('_':['0'..'9'])) s

opSyms :: String
opSyms = ":!#$%&*+./<=>?@|^-~\\{}[]"


-- | Merging
allocate :: Eq a => [[a]] -> [a]
allocate []       = []
allocate (xs:xss) = merge xs (allocate xss)

merge :: Eq a => [a] -> [a] -> [a]
merge xs (y:ys) = y:merge (delete y xs) ys
merge xs []     = xs

prop_merge_extends :: [Int] -> [Int] -> Bool
prop_merge_extends xs ys = ys `isPrefixOf` merge xs ys

prop_merge_idem :: [Int] -> Bool
prop_merge_idem xs = xs `merge` xs == xs

isSubsetOf :: Eq a => [a] -> [a] -> Bool
[]     `isSubsetOf` ys = True
(x:xs) `isSubsetOf` ys = x `elem` ys && xs `isSubsetOf` delete x ys

prop_merge_adds :: [Int] -> [Int] -> Bool
prop_merge_adds xs ys = xs `isSubsetOf` merge xs ys

prop_merge_lengths :: [Int] -> [Int] -> Bool
prop_merge_lengths xs ys = length (xs `merge` ys) == length ys + length (xs \\ ys)

prop_allocate :: [[Int]] -> Bool
prop_allocate xss = all (`isSubsetOf` allocate xss) xss

return []

tests :: IO Bool
tests = $quickCheckAll

