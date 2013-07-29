module IWC where

import Prelude (Bool(..))

data Nat = S Nat | Z

len [] = Z
len (x:xs) = S (len xs)

even Z = True
even (S Z) = False
even (S (S x)) = even x

[] `app` ys = ys
(x:xs) `app` ys = x : (xs `app` ys)


rotate Z xs = xs
rotate (S n) [] = []
rotate (S n) (x:xs) = rotate n (xs `app` [x])


plus x Z = x
plus x (S y) = S (plus x y)

times x Z = Z
times x (S y) = (x `times` y) `plus` x

choose x Z = S Z
choose Z (S y) = Z
choose (S x) (S y) = choose x (S y) `plus` choose x y

exp x Z = Z
exp x (S y) = exp x y `times` x

lt x Z = False
lt Z y = True
lt (S x) (S y) = lt x y

sum' :: Nat -> Nat -> (Nat -> Nat) -> Nat
sum' x Z f = f Z
sum' x (S y) f | S y `lt` x = Z
               | True = f (S y) `plus` sum' x y f

minus n Z = n
minus (S n) (S k) = minus n k
minus Z k = Z

evenm Z = True
evenm (S n) = oddm n

oddm Z = False
oddm (S n) = evenm n

evenr Z = True
evenr (S Z) = False
evenr (S (S x)) = evenr x

is6 (S (S (S (S (S (S Z)))))) = True
is6 _ = False

splitList :: [a] -> [a] -> [a]
splitList [] w = w
splitList (a:x) w | is6 (len w) = w `app` splitList (a:x) []
                  | True = splitList x (w `app` [a])

newSplit :: [a] -> [a] -> Nat -> [a]
newSplit [] w d = w
newSplit (a:x) w d | is6 d = w `app` newSplit (a:x) [] Z
                   | True = newSplit x (w `app` [a]) (S d)

