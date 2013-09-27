module Guards where

data Nat = Z | S Nat

eq ::  Nat -> Nat -> Bool
eq Z Z = True
eq (S x) (S y) = eq x y
eq _ _ = False

plus ::  Nat -> Nat -> Nat
plus Z     x = x
plus (S y) x = S (plus y x)

eeep :: Nat -> Nat -> ()
eeep x y | (x `plus` y) `eq` (y `plus` x) = ()
