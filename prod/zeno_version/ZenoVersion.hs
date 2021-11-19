{-

    Zeno version of Productive Use of Failure testsuite

-}
module ZenoVersion where

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

-- Theorems

prop_T01 :: Nat -> Prop
prop_T01 x = prove (double x :=: x + x)

prop_T02 :: [a] -> [a] -> Prop
prop_T02 x y = prove (length (x ++ y ) :=: length (y ++ x))

prop_T03 :: [a] -> [a] -> Prop
prop_T03 x y = prove (length (x ++ y ) :=: length (y ) + length x)

prop_T04 :: [a] -> Prop
prop_T04 x = prove (length (x ++ x) :=: double (length x))

prop_T05 :: [a] -> Prop
prop_T05 x = prove (length (rev x) :=: length x)

prop_T06 :: [a] -> [a] -> Prop
prop_T06 x y = prove (length (rev (x ++ y )) :=: length x + length y)

prop_T07 :: [a] -> [a] -> Prop
prop_T07 x y = prove (length (qrev x y) :=: length x + length y)

prop_T08 :: Nat -> Nat -> [a] -> Prop
prop_T08 x y z = prove (drop x (drop y z) :=: drop y (drop x z))

prop_T09 :: Nat -> Nat -> [a] -> Nat -> Prop
prop_T09 x y z w = prove (drop w (drop x (drop y z)) :=: drop y (drop x (drop w z)))

prop_T10 :: [a] -> Prop
prop_T10 x = prove (rev (rev x) :=: x)

prop_T11 :: [a] -> [a] -> Prop
prop_T11 x y = prove (rev (rev x ++ rev y) :=: y ++ x)

prop_T12 :: [a] -> [a] -> Prop
prop_T12 x y = prove (qrev x y :=: rev x ++ y)

prop_T13 :: Nat -> Prop
prop_T13 x = prove (half (x + x) :=: x)

prop_T14 :: [Nat] -> Prop
prop_T14 x = proveBool (sorted (isort x))

prop_T15 :: Nat -> Prop
prop_T15 x = prove (x + S x :=: S (x + x))

prop_T16 :: Nat -> Prop
prop_T16 x = proveBool (even (x + x))

prop_T17 :: [a] -> [a] -> Prop
prop_T17 x y = prove (rev (rev (x ++ y)) :=: rev (rev x) ++ rev (rev y))

prop_T18 :: [a] -> [a] -> Prop
prop_T18 x y = prove (rev (rev x ++ y) :=: rev y ++ x)

prop_T19 :: [a] -> [a] -> Prop
prop_T19 x y = prove (rev (rev x) ++ y :=: rev (rev (x ++ y)))

prop_T20 :: [a] -> Prop
prop_T20 x = proveBool (even (length (x ++ x)))

prop_T21 :: [a] -> [a] -> Prop
prop_T21 x y = prove (rotate (length x) (x ++ y) :=: y ++ x)

prop_T22 :: [a] -> [a] -> Prop
prop_T22 x y = prove (even (length (x ++ y)) :=: even (length (y ++ x)))

prop_T23 :: [a] -> [a] -> Prop
prop_T23 x y = prove (half (length (x ++ y)) :=: half (length (y ++ x)))

prop_T24 :: Nat -> Nat -> Prop
prop_T24 x y = prove (even (x + y) :=: even (y + x))

prop_T25 :: [a] -> [a] -> Prop
prop_T25 x y = prove (even (length (x ++ y)) :=: even (length y + length x))

prop_T26 :: Nat -> Nat -> Prop
prop_T26 x y = prove (half (x + y) :=: half (y + x))

prop_T27 :: [a] -> Prop
prop_T27 x = prove (rev x :=: qrev x [])

prop_T28 :: [[a]] -> Prop
prop_T28 x = prove (revflat x :=: qrevflat x [])

prop_T29 :: [a] -> Prop
prop_T29 x = prove (rev (qrev x []) :=: x)

prop_T30 :: [a] -> Prop
prop_T30 x = prove (rev (rev x ++ []) :=: x)

prop_T31 :: [a] -> Prop
prop_T31 x = prove (qrev (qrev x []) [] :=: x)

prop_T32 :: [a] -> Prop
prop_T32 x = prove (rotate (length x) x :=: x)

prop_T33 :: Nat -> Prop
prop_T33 x = prove (fac x :=: qfac x one)

prop_T34 :: Nat -> Nat -> Prop
prop_T34 x y = prove (x * y :=: mult x y zero)

prop_T35 :: Nat -> Nat -> Prop
prop_T35 x y = prove (exp x y :=: qexp x y one)

prop_T36 :: Nat -> [Nat] -> [Nat] -> Prop
prop_T36 x y z = givenBool (x `elem` y) (proveBool (x `elem` (y ++ z)))

prop_T37 :: Nat -> [Nat] -> [Nat] -> Prop
prop_T37 x y z = givenBool (x `elem` z) (proveBool (x `elem` (y ++ z)))

prop_T38 :: Nat -> [Nat] -> [Nat] -> Prop
prop_T38 x y z = givenBool (x `elem` y)
               ( givenBool (x `elem` z)
               ( proveBool (x `elem` (y ++ z))))

prop_T39 :: Nat -> Nat -> [Nat] -> Prop
prop_T39 x y z = givenBool (x `elem` drop y z) (proveBool (x `elem` z))

prop_T40 :: [Nat] -> [Nat] -> Prop
prop_T40 x y = givenBool (x `subset` y) $ prove ((x `union` y) :=: y)

prop_T41 :: [Nat] -> [Nat] -> Prop
prop_T41 x y = givenBool (x `subset` y) $ prove ((x `intersect` y) :=: x)

prop_T42 :: Nat -> [Nat] -> [Nat] -> Prop
prop_T42 x y z = givenBool (x `elem` y) (proveBool (x `elem` (y `union` z)))

prop_T43 :: Nat -> [Nat] -> [Nat] -> Prop
prop_T43 x y z = givenBool (x `elem` y) (proveBool (x `elem` (z `union` y)))

prop_T44 :: Nat -> [Nat] -> [Nat] -> Prop
prop_T44 x y z = givenBool (x `elem` y)
               ( givenBool (x `elem` z)
               ( proveBool (x `elem` (y `intersect` z))))

prop_T45 :: Nat -> [Nat] -> Prop
prop_T45 x y = proveBool (x `elem` insert x y)

prop_T46 :: Nat -> Nat -> [Nat] -> Prop
prop_T46 x y z = given (x :=: y)
               $ proveBool (x `elem` insert y z)

prop_T47 :: Nat -> Nat -> [Nat] -> Prop
prop_T47 x y z = givenBool (x /= y) $ prove ((x `elem` insert y z) :=: x `elem` z)

prop_T48 :: [Nat] -> Prop
prop_T48 x = prove (length (isort x) :=: length x)

prop_T49 :: Nat -> [Nat] -> Prop
prop_T49 x y = givenBool (x `elem` isort y) (proveBool (x `elem` y))

prop_T50 :: Nat -> [Nat] -> Prop
prop_T50 x y = prove (count x (isort y) :=: count x y)

