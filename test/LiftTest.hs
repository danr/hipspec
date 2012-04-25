module LiftTest where

import Prelude (Bool(..),undefined)

data Nat = Z | S Nat

plus :: Nat -> Nat -> Nat
plus Z     y = y
plus (S x) y = S (plus x y)

-- Introduces a lifted g
f x = let {-# NOINLINE g #-}
          g y = x `plus` y
      in  g x `plus` g (x `plus` x)

-- Here, g is nicely inlined
h x = let g y = x `plus` y
      in  g x `plus` g (x `plus` x)


