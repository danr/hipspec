{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
module Main where

import Control.Applicative hiding (empty)

import Data.Function
import Data.Typeable

import Test.QuickCheck 
import Test.QuickSpec hiding (size)
import Hip.HipSpec hiding (size)

-- Invariant : front is never empty unless back also is
data Queue = Queue { front :: [Int] , back :: [Int] }
  deriving (Show,Typeable)

-- Equality and Ordering is by lists
instance Eq Queue where           
  (==) = (==) `on` toList
  
instance Ord Queue where
  compare = compare `on` toList

instance Arbitrary Queue where
  arbitrary = sized $ \s ->
    frequency [(0,return (Queue [] []))
              ,(s,(\x xs ys -> Queue (x:xs) ys) <$> arbitrary
                                                <*> arbitrary
                                                <*> arbitrary)
              ]

instance Classify Queue where
  type Value Queue = Queue
  evaluate = return

invariant :: Queue -> Bool
invariant (Queue front back) = not (null front) || null back

empty :: Queue
empty = Queue [] []

enqueue :: Int -> Queue -> Queue
enqueue x (Queue [] []) = Queue [x] []
enqueue x (Queue f  b ) = Queue f (x:b)

top :: Queue -> Int
top (Queue []     _) = error "top: empty queue"
top (Queue (x:xs) _) = x

pop :: Queue -> Queue
pop (Queue [x]    b)  = Queue (reverse b) []
pop (Queue (x:xs) b)  = Queue xs b
pop (Queue []     []) = error "pop: empty queue"
pop (Queue []     b)  = error "pop: broken invariant"

fromList :: [Int] -> Queue
fromList xs = Queue xs []

toList :: Queue -> [Int]
toList (Queue f b) = f ++ reverse b

size :: Queue -> Int
size (Queue f b) = length f + length b

{-
 Many nice properties:
 invariant q          == True, which means that the generator is sound
 fromList (toList q)  == q
 toList (fromList xs) == xs
 toList q ++ [x]      == toList (enqueue x q)

 It would be nice if we could filter away those only concerning
 (++), (:), [], head, tail, init, last, and only focus on the queue-relevant

 Case study:
  (I) First invariant q == True was missing, had to fix generator.

  (II)
   Something is wrong, also missing:
     invariant (pop q) == True
     invariant (enqueue x q) == True... Maybe because they are pruned?
   Yes! Commenting out things gives
     invariant q == empty, comment away empty
     invariant q == invariant q', comment away q'
     invariant q == invariant (enqueue x q) :D

    Then removing enqueue, 
     invariant (fromList xs) == invariant q,
    removing fromList then no more invariants! i.e. pop does not hold
    the invaraint!
    The problem is that pop is undefined on empty queues, so
    undefined /= True. Patching the generator for only non-empty queues
    fixes this
 
 (III)
   Missing
     top (enqueue x q) == x
     pop (enqueue x q) == q
   But we have
     top (enqueue x empty) == x
     pop (enqueue x empty) == empty
   First I thought this is also because of top and pop being undefined 
   on empty lists (?)

   But at a second thought, this is true for stacks but not queues
   (duuuh). Been coding for too long.

 (IV)
   Increasing the term depth to 4 gives some other crazy properties
     top (enqueue x (pop q)) == top (pop (enqueue x q))
     enqueue (top q) (enqueue x (pop q)) == pop (enqueue (top q) (enqueue x q))
  
-}

prop_pop_invariant :: Queue -> Bool
prop_pop_invariant q = invariant (pop q)

-- These properties are not true
prop_pop :: Queue -> Int -> Bool
prop_pop q x = pop (enqueue x q) == q

prop_top :: Queue -> Int -> Bool
prop_top q x = top (enqueue x q) == x


queueSpec = describe "Queue"
                [ var "q"         empty
                , var "q'"        empty
                , var "x"         intType
                , var "y"         intType
                , var "xs"        listType
                , var "ys"        listType       
                , con "[]"        ([]      :: [Int])
                , con ":"         ((:)     :: Int -> [Int] -> [Int])
                , con "++"        ((++)    :: [Int] -> [Int] -> [Int])
                , con "head"      (head    :: [Int] -> Int)
                , con "last"      (last    :: [Int] -> Int)
                , con "tail"      (tail    :: [Int] -> [Int])
                , con "init"      (init    :: [Int] -> [Int])
                , con "empty"     empty
                , con "enqueue"   enqueue
                , con "top"       top
                , con "pop"       pop
                , con "invariant" invariant
--                , con "True"      True
                , con "fromList"  fromList
                , con "toList"    toList
                , con "size"      size
                ]
  where
    intType   = undefined :: Int
    listType  = undefined :: [Int]

-- main = quickSpecDepth queueSpec 3
main = hipSpec "Queue.hs" queueSpec 3
