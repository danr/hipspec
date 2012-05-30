-- Examples from
-- http://www.csc.liv.ac.uk/~lad/research/challenges

module IWC where

import HipPrelude
data Nat = S Nat | Z


(=:=) :: a -> a -> a
(=:=) = (=:=)

otherwise = True

len [] = Z
len (x:xs) = S (len xs)

even Z = True
even (S Z) = False
even (S (S x)) = even x

[]     `app` ys = ys
(x:xs) `app` ys = x : (xs `app` ys)

prop_evenLengthAppend :: [a] -> [a] -> Prop [a]
prop_evenLengthAppend xs ys = even (len (xs `app` ys) =:=
                                     even (len (ys `app` xs)))

rotate Z     xs     = xs
rotate (S n) []     = []
rotate (S n) (x:xs) = rotate n (xs `app` [x])

prop_rotateLength :: [a] -> Prop [a]
prop_rotateLength xs = rotate (len xs) xs =:= xs

prop_rotateLength2 :: [a] -> [a] -> Prop [a]
prop_rotateLength2 xs ys = rotate (len xs) (xs `app` ys
                                              =:= (ys `app` xs))

plus x Z     = x
plus x (S y) = S (plus x y)

times x Z     = Z
times x (S y) = (x `times` y) `plus` x

choose x     Z     = S Z
choose Z     (S y) = Z
choose (S x) (S y) = choose x (S y) `plus` choose x y

exp x Z     = Z
exp x (S y) = exp x y `times` x

lt x     Z     = False
lt Z     y     = True
lt (S x) (S y) = lt x y

sum' :: Nat -> Nat -> (Nat -> Nat) -> Nat
sum' x Z     f = f Z
sum' x (S y) f | S y `lt` x = Z
               | otherwise  = f (S y) `plus` sum' x y f

prop_binomialTheorems :: Nat -> Nat -> Prop Nat
prop_binomialTheorems x n = exp (S x) n =:= sum' Z n (\i -> choose n i `times` exp x i)

minus n Z = n
minus (S n) (S k) = minus n k
minus Z k = Z

{-
prop_chooseLemma :: Nat -> Nat -> Prop Nat
prop_chooseLemma n k = givenBool (k `lt` n)
                     $ choose n k =:= choose n (n `minus` k)
-}

prop_sumLemma :: Nat -> Nat -> (Nat -> Nat) -> (Nat -> Nat) -> Prop Nat
prop_sumLemma n m f g = sum' n m (\i -> f i `plus` g i) =:= sum' n m f `plus` sum' n m g

prop_sumLemma2 :: Nat -> Nat -> Nat -> (Nat -> Nat) -> Prop Nat
prop_sumLemma2 n m t f = sum' n m (\i -> t `times` f i) =:= t `times` sum' n m f

evenm Z     = True
evenm (S n) = oddm n

oddm Z      = False
oddm (S n)  = evenm n

evenr Z = True
evenr (S Z) = False
evenr (S (S x)) = evenr x

prop_evenEq :: Nat -> Prop Bool
prop_evenEq n = evenm n =:= evenr n

is6 (S (S (S (S (S (S Z)))))) = True
is6 _                         = False

splitList :: [a] -> [a] -> [a]
splitList [] w = w
splitList (a:x) w | is6 (len w) = w `app` splitList (a:x) []
                  | otherwise   = splitList x (w `app` [a])

newSplit :: [a] -> [a] -> Nat -> [a]
newSplit []    w d = w
newSplit (a:x) w d | is6 d     = w `app` newSplit (a:x) [] Z
                   | otherwise = newSplit x (w `app` [a]) (S d)

prop_split :: [a] -> [a] -> Prop [a]
prop_split x w = newSplit x w (len w) =:= splitList x w