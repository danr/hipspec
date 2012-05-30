module Sequences where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),take)

data Nat = Z | S Nat
  deriving (Eq,Ord,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,25)

Z     + y = y
(S x) + y = S (x + y)

Z     * _ = Z
(S x) * y = y + (x * y)

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

zero,one :: Nat
zero = Z
one = S Z

enumFrom :: Nat -> [Nat]
enumFrom x = x : enumFrom (S x)

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

tail :: [a] -> [a]
tail (_:xs) = xs

-- Factorials -----------------------------------------------------------------

facts :: [Nat]
facts = one : zipWith (*) (enumFrom one) facts

fact :: Nat -> Nat
fact Z     = one
fact (S n) = S n * fact n

facts' :: [Nat]
facts' = map fact (enumFrom zero)

prop_facts :: Prop [Nat]
prop_facts = facts =:= facts'

-- Fibonacci ------------------------------------------------------------------

fibs :: [Nat]
fibs = zero : one : zipWith (+) fibs (tail fibs)

fib :: Nat -> Nat
fib Z         = zero
fib (S Z)     = one
fib (S (S n)) = fib n + fib (S n)

fibs' :: [Nat]
fibs' = map fib (enumFrom zero)

prop_fibs :: Prop [Nat]
prop_fibs = fibs =:= fibs'


main = do
  quickCheck (printTestCase "prop_facts" (prop_facts :: Prop [Nat]))
  quickCheck (printTestCase "prop_fibs"  (prop_fibs  :: Prop [Nat]))
