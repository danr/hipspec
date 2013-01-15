module PropT19 where

import Prelude(Bool(..))
import Zeno

-- Definitions

True && x = x
_    && _ = False

False || x = x
_     || _ = True

not True = False
not False = True

-- Nats

data Nat = S Nat | Z

(+) :: Nat -> Nat -> Nat
Z + y = y
(S x) + y = S (x + y)

(*) :: Nat -> Nat -> Nat
Z * _ = Z
(S x) * y = y + (x * y)

(==),(/=) :: Nat -> Nat -> Bool
Z   == Z   = True
Z   == _   = False
S _ == Z   = False
S x == S y = x == y

x /= y = not (x == y)

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
_   <= Z   = False
S x <= S y = x <= y

one, zero :: Nat
zero = Z
one = S Z

double :: Nat -> Nat
double Z = Z
double (S x) = S (S (double x))

even :: Nat -> Bool
even Z = True
even (S Z) = False
even (S (S x)) = even x

half :: Nat -> Nat
half Z = Z
half (S Z) = Z
half (S (S x)) = S (half x)

mult :: Nat -> Nat -> Nat -> Nat
mult Z _ acc = acc
mult (S x) y acc = mult x y (y + acc)

fac :: Nat -> Nat
fac Z = S Z
fac (S x) = S x * fac x

qfac :: Nat -> Nat -> Nat
qfac Z acc = acc
qfac (S x) acc = qfac x (S x * acc)

exp :: Nat -> Nat -> Nat
exp _ Z = S Z
exp x (S n) = x * exp x n

qexp :: Nat -> Nat -> Nat -> Nat
qexp x Z acc = acc
qexp x (S n) acc = qexp x n (x * acc)

-- Lists

length :: [a] -> Nat
length [] = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

drop :: Nat -> [a] -> [a]
drop Z     xs     = xs
drop _     []     = []
drop (S x) (_:xs) = drop x xs

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

revflat :: [[a]] -> [a]
revflat []           = []
revflat ([]:xss)     = revflat xss
revflat ((x:xs):xss) = revflat (xs:xss) ++ [x]

qrevflat :: [[a]] -> [a] -> [a]
qrevflat []           acc = acc
qrevflat ([]:xss)     acc = qrevflat xss acc
qrevflat ((x:xs):xss) acc = qrevflat (xs:xss) (x:acc)

rotate :: Nat -> [a] -> [a]
rotate Z xs = xs
rotate _ [] = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) = n == x || elem n xs

subset :: [Nat] -> [Nat] -> Bool
subset [] ys = True
subset (x:xs) ys = x `elem` xs && subset xs ys

intersect,union :: [Nat] -> [Nat] -> [Nat]
(x:xs) `intersect` ys | x `elem` ys = x:(xs `intersect` ys)
                      | otherwise = xs `intersect` ys
[] `intersect` ys = []

union (x:xs) ys | x `elem` ys = union xs ys
                | otherwise = x:(union xs ys)
union [] ys = ys

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

count :: Nat -> [Nat] -> Nat
count n (x:xs) | n == x = S (count n xs)
               | otherwise = count n xs
count n [] = Z

sorted :: [Nat] -> Bool
sorted (x:y:xs) = x <= y && sorted (y:xs)
sorted _ = True

-- Theorem

prop_T19 :: [a] -> [a] -> Prop
prop_T19 x y = prove (rev (rev x) ++ y :=: rev (rev (x ++ y)))
