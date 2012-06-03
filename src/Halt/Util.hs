module Halt.Util
    (
    -- * Convenience reexports
      module Control.Arrow
    , module Control.Applicative

    -- * Function composition
    , (.:)

    -- * Boolean inspection
    , (?)

    -- * Monadic concatenative combinators
    , concatMapM
    , concatFoldM

    -- * Cursored traversals of lists
    , selections
    , inspect
    , withPrevious
    , uniqueCartesian

    -- * Efficient nub and group
    , nubSorted
    , groupSortedOn
    , nubSortedOn

    -- * Intersection
    , intersects

    -- * Printing in colour and bold
    , Colour(..)
    , colour
    , bold
    , normal
    ) where

import Control.Arrow       ((***),(&&&),first,second)
import Control.Applicative ((<$>),(<*>),Applicative)

import Control.Monad (liftM)

import Data.List
import Data.Function (on)
import Data.Ord      (comparing)

infixr 9 .:

-- | Function composition deluxe
--   (f .: g) = \x y -> f (g x y)
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

-- | Pair up a list with its previous and next elements
--
-- @
--     selections "abc" = [("",'a',"bc"),("a",'b',"c"),("ab",'c',"")]
-- @
selections :: [a] -> [([a],a,[a])]
selections xs = map (fromSplit . (`splitAt` xs)) [0..length xs-1]
  where fromSplit (as,b:bs) = (as,b,bs)
        fromSplit _         = error "selections fromSplit unreachable"

-- | Pair up a list with the element and the rest of the elements
--
-- @
--     inspect "abc" = [('a',"bc"),('b',"ac"),('c',"ab")]
-- @
inspect :: [a] -> [(a,[a])]
inspect = map (\(i,x,r) -> (x,i++r)) . selections

-- | Pair up a list with its previous elements
--
-- @
--     withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
-- @
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

-- | Non-reflexive and non-symmetric cartesian product
--
-- @
--     uniqueCartesian "abc" = [('a','b'),('a','c'),('b','c')]
-- @
uniqueCartesian :: [a] -> [(a,a)]
uniqueCartesian as = concat [ zip (repeat x) xs | (x,xs) <- inspect as ]

-- | /O(n log n)/ nub, but destroys ordering
nubSorted :: Ord a => [a] -> [a]
nubSorted = map head . group . sort

-- | /O(n log n)/ group, but destroys ordering
groupSortedOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortedOn f = groupBy ((==) `on` f)
                . sortBy (comparing f)

-- | /O(n log n)/ nub by a comparison function. Destroys ordering
nubSortedOn :: Ord b => (a -> b) -> [a] -> [a]
nubSortedOn f = map head . groupSortedOn f

-- | Do these two lists have a non-empty intersection?
intersects :: Eq a => [a] -> [a] -> Bool
intersects = (not . null) .: intersect

data Colour = Red | Green | Blue | Pink | Yellow | Turquoise

-- | Print with colour
colour :: Colour -> String -> String
colour c s = fgcol ++ s ++ normal
  where
    fgcol :: String
    fgcol = "\ESC[0" ++ show (30+col2num) ++ "m"

    col2num :: Int
    col2num = case c of
      Red       -> 1
      Green     -> 2
      Yellow    -> 3
      Blue      -> 4
      Pink      -> 5
      Turquoise -> 7

-- | Print in bold
bold :: String -> String
bold = ("\ESC[1m" ++)

-- | Print normally
normal :: String
normal = "\ESC[0m"



