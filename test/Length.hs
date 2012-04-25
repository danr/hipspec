module Length where

import Prelude()

data Nat = Succ Nat | Zero

(+) :: Nat -> Nat -> Nat
Succ m + n = Succ (m + n)
Zero   + n = Zero

infixr 5 ++

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = []

length :: [a] -> Nat
length []     = Zero
length (_:xs) = Succ (length xs)