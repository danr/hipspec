{-# LANGUAGE TypeFamilies, DeriveDataTypeable #-}
module Main where

import qualified Data.List as L
import Data.Maybe
import Data.Function
import Data.Typeable
import Control.Applicative hiding (empty)

import Test.QuickSpec hiding (size)
import Test.QuickCheck 

data PQ = PQ { toList :: [Int] }
  deriving (Typeable,Show)

invariant :: PQ -> Bool
invariant (PQ xs) = and (zipWith (<=) xs (drop 1 xs))

insert :: Int -> PQ -> PQ
insert x (PQ xs) = PQ (L.insert x xs)

top :: PQ -> Int
top (PQ (x:xs)) = x
top _           = error "top: empty PQ"

pop :: PQ -> PQ
pop (PQ (x:xs)) = PQ xs
pop _           = error "pop: empty PQ"

topM :: PQ -> Maybe Int
topM = listToMaybe . toList

popM :: PQ -> Maybe PQ
popM (PQ (x:xs)) = Just (PQ xs)
popM _           = Nothing

isEmpty :: PQ -> Bool
isEmpty = null . toList

empty :: PQ
empty = PQ []

fromList :: [Int] -> PQ
fromList = PQ . L.sort

size :: PQ -> Int
size = length . toList

-- Equality and Ordering is by lists
instance Eq PQ where           
  (==) = (==) `on` toList
  
instance Ord PQ where
  compare = compare `on` toList

instance Arbitrary PQ where
  arbitrary = PQ . L.sort <$> arbitrary

instance Classify PQ where
  type Value PQ = PQ
  evaluate = return

pqSpec = describe "NaivePQ"
                [ var "q"         empty
--                , var "p"         empty
                , var "x"         intType
--                , var "y"         intType
                , var "xs"        listType
--                , var "ys"        listType       
                , con "[]"        ([]      :: [Int])
                , con ":"         ((:)     :: Int -> [Int] -> [Int])
                , con "++"        ((++)    :: [Int] -> [Int] -> [Int])
{-                , con "head"      (head    :: [Int] -> Int)
                , con "last"      (last    :: [Int] -> Int)
                , con "tail"      (tail    :: [Int] -> [Int])
                , con "init"      (init    :: [Int] -> [Int])
-}
                , con "empty"     empty
                , con "insert"    insert
                , con "top"       top
                , con "pop"       pop
--                , con "topM"      topM
--                , con "popM"      popM
--                , con "fromMaybe" (fromMaybe :: Int -> Maybe Int -> Int)
--                , con "fromMaybe" (fromMaybe :: PQ  -> Maybe PQ  -> PQ)
                , con "invariant" invariant
                , con "fromList"  fromList
                , con "toList"    toList
                , con "sort"      (L.sort :: [Int] -> [Int])
                , con "size"      size
                , con "succ"      (succ :: Int -> Int)
                , con "+"         ((+) :: Int -> Int -> Int)
                ]
  where
    intType   = undefined :: Int
    listType  = undefined :: [Int]

main = quickSpecDepth pqSpec 3





