module Queues where

import HipPrelude
import Prelude (Eq((==)),Ord,Show,iterate,(!!),fmap,Bool(..),Int,return)

-- Invariant : front is never empty unless back also is
-- We cannot currently express this in logic?
data Queue a = Queue [a] [a] -- front, then back
  deriving Show

-- Equality and Ordering is by lists: {-# OPTIONS_EQUALITY Queue toList #-}
instance Eq a => Eq (Queue a) where
  q == q' = toList q == toList q'

instance Arbitrary a => Arbitrary (Queue a) where
  arbitrary = sized (\s ->def_2
    frequency [(0,return (Queue [] []))
              ,(s,do x  <- arbitrary
                     xs <- arbitrary
                     ys <- arbitrary
                     return (Queue (x:xs) ys))
              ])

data Nat = Z | S Nat deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,25)

Z     + y = y
(S x) + y = S (x + y)

--instance Classify Queue where
--  type Value Queue = Queue
--  evaluate = return

--undefined :: a
--undefined = f True where f False = f False

null :: [a] -> Bool
null [] = True
null _  = False

invariant :: Queue a -> Bool
invariant (Queue front back) = null front --> null back

(-->) :: Bool -> Bool -> Bool
True --> False = False
_    --> _     = True

empty :: Queue a
empty = Queue [] []

enqueue :: a -> Queue a -> Queue a
enqueue x (Queue [] []) = Queue [x] []
enqueue x (Queue f  b ) = Queue f (x:b)

top :: Queue a -> a
top (Queue []     _) = undefined -- "top: empty queue"
top (Queue (x:xs) _) = x

pop :: Queue a -> Queue a
pop (Queue [x]    b)  = Queue (reverse b) []
pop (Queue (x:xs) b)  = Queue xs b
pop (Queue []     []) = undefined -- "pop: empty queue"
pop (Queue []     b)  = undefined -- "pop: broken invariant"

fromList :: [a] -> Queue a
fromList xs = Queue xs []

toList :: Queue a -> [a]
toList (Queue f b) = f ++ reverse b

size :: Queue a -> Nat
size (Queue f b) = length f + length b

length :: [a] -> Nat
length [] = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

head :: [a] -> a
head (x:xs) = x

tail :: [a] -> [a]
tail (x:xs) = xs

last :: [a] -> a
last [x]    = x
last (x:xs) = last xs

init :: [a] -> [a]
init [x]    = []
init (x:xs) = x:init xs

reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

prop_1 :: Queue a -> Prop a
prop_1 q         = top q =:= head (toList q)

prop_2 :: [a] -> Prop a
prop_2 xs        = head xs =:= top (fromList xs)

prop_7 :: Prop a
prop_7          = top empty =:= undefined

prop_8 :: Prop (Queue a)
prop_8          = pop empty =:= undefined

prop_9 :: Prop (Queue a)
prop_9          = fromList [] =:= empty

prop_10 :: Prop [Bool]
prop_10         = toList empty =:= []

prop_14 :: a -> Queue a -> Prop Bool
prop_14 x q     = invariant (enqueue x q) =:= invariant q

prop_15 :: a -> a -> Queue a -> Prop Nat
prop_15 x y q   = size (enqueue y q) =:= size (enqueue x q)

prop_18 :: Queue a -> Prop a
prop_18 q       = head (toList q) =:= top q

prop_19 :: [a] -> Prop [a]
prop_19 xs      = init (tail xs) =:= tail (init xs)

prop_20 :: [a] -> Prop a
prop_20 xs      = top (fromList xs) =:= head xs

prop_21 :: Queue a -> Queue a -> Prop Bool
prop_21 q q'    = invariant (pop q') =:= invariant (pop q)

prop_22 :: [a] -> Prop Bool
prop_22 xs      = invariant (fromList xs) =:= invariant empty

prop_23 :: [a] -> Prop (Queue a)
prop_23 xs      = fromList (tail xs) =:= pop (fromList xs)

prop_24 :: Queue a -> Prop (Queue a)
prop_24 q       = fromList (toList q) =:= q

prop_25 :: Queue a -> Prop [a]
prop_25 q       = toList (pop q) =:= tail (toList q)

prop_26 :: [a] -> Prop [a]
prop_26 xs      = toList (fromList xs) =:= xs

prop_27 :: [a] -> Prop [a]
prop_27 xs       = toList (fromList xs) =:= xs

prop_28 :: Queue a -> Prop Bool
prop_28 q        = invariant q =:= True

prop_34 :: a -> Prop a
prop_34 x        = top (enqueue x empty) =:= x

prop_35 :: a -> a -> Prop (Queue a)
prop_35 x q      = pop (enqueue x empty) =:= empty

prop_36 :: a -> Prop (Queue a)
prop_36 x         = fromList (x:[]) =:= enqueue x empty

prop_37 :: a -> Queue a -> Prop [a]
prop_37 x q      = toList q++(x:[]) =:= toList (enqueue x q)

