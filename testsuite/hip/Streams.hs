-- Based on Ralf Hinze's paper Concrete Stream Calculus, but so far
-- only the first few pages.
module Streams where

import HipPrelude
import Prelude (Show,show,take,(.),succ)

data Stream a = a :< Stream a

instance Show a => Show (Stream a) where
  show = show . take 10 . toList
    where
      toList (x :< xs) = x : toList xs

pure :: a -> Stream a
pure a = a :< pure a

(<*>) :: Stream (a -> b) -> Stream a -> Stream b
(f :< fs) <*> (x :< xs) = f x :< (fs <*> xs)

(<$>) :: (a -> b) -> Stream a -> Stream b
fs <$> xs = pure fs <*> xs

data Nat = Z | S Nat

instance Show Nat where
  show = show . toNum
    where
      toNum Z     = 0
      toNum (S x) = succ (toNum x)

Z     +. y = y
(S x) +. y = S (x +. y)

Z     *. _ = Z
(S x) *. y = y +. (x *. y)

(+) :: Stream Nat -> Stream Nat -> Stream Nat
xs + ys = (+.) <$> xs <*> ys

(*) :: Stream Nat -> Stream Nat -> Stream Nat
xs * ys = (*.) <$> xs <*> ys

zero :: Stream Nat
zero = pure Z

one :: Stream Nat
one = pure (S Z)

prop_one :: Prop (Stream Nat)
prop_one = S <$> zero =:= one

nat :: Stream Nat
nat = Z :< (nat + one)

fac :: Stream Nat
fac = S Z :< ((nat + one) * fac)

tail :: Stream a -> Stream a
tail (_ :< xs) = xs

fib,fib' :: Stream Nat
fib  = Z   :< fib'
fib' = S Z :< (fib + fib')

fib'' :: Stream Nat
fib'' = Z :< ((S Z :< fib'') + fib'')

prop_fib_def_eq :: Prop (Stream Nat)
prop_fib_def_eq = fib =:= fib''

(\/) :: Stream a -> Stream a -> Stream a
(x:<xs) \/ ys = x :< (ys \/ xs)

two :: Stream Nat
two = pure (S (S Z))

bin :: Stream Nat
bin = Z :< ((two * bin + one) \/ (two * bin + two))

prop_bin_nat :: Prop (Stream Nat)
prop_bin_nat = bin =:= nat