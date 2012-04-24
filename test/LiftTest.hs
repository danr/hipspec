module LiftTest where

import Prelude (Bool(..),undefined)

data Nat = Z | S Nat

--Z     <= _     = True
--_     <= Z     = False
--(S x) <= (S y) = x <= y

{-# NOINLINE plus #-}
plus :: Nat -> Nat -> Nat
plus Z     y = y
plus (S x) y = S (plus x y)

f x = let {-# NOINLINE g #-}
          g y = x `plus` y
      in  g x `plus` g (x `plus` x)

--even Z = True
--even (S x) = odd x
--
--odd Z = False
--odd (S x) = even x