

-- use
--




{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable #-}

module Main where

import Prelude (Bool(..),error,toEnum,fromEnum,pred,succ,sqrt,round
               ,Enum,Eq,Ord,Show,return,(.),undefined)
import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Data.Typeable

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized (\s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x))

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return

-- data Prop a = Equals a a --
type Prop a = a

infix 0 =:=

(=:=) :: a -> a -> Prop a
(=:=) = (=:=)

proveBool :: Bool -> Prop Bool
proveBool = (=:= True)

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)
-- data Tree a = Leaf | Node (Tree a) a (Tree a) deriving (Eq,Ord,Show,Typeable)

-- Boolean functions

-- not :: Bool -> Bool
-- not True = False
-- not False = True
--
(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- (||) :: Bool -> Bool -> Bool
-- False || False = False
-- _    || _    = True

-- Natural numbers

Z     == Z     = True
(S x) == (S y) = x == y
_     == _     = False

Z     <= _     = True
(S x) <= (S y) = x <= y
_     <= _     = False

Z     < _     = True
(S x) < (S y) = x < y
_     < _     = False

Z     + y = y
(S x) + y = S (x + y)

-- Z     - _     = Z
-- x     - Z     = x
-- (S x) - (S y) = x - y

-- min Z     y     = Z
-- min (S x) Z     = Z
-- min (S x) (S y) = S (min x y)
--
-- max Z     y     = y             --
-- max x     Z     = x
-- max (S x) (S y) = S (max x y)

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) | n == x = True
elem n (x:xs) = elem n xs
--   case n == x of
--     True -> True
--     _ -> elem n xs

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take :: Nat -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _    -> x:xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _    -> filter p xs

butlast :: [a] -> [a]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insort n xs)

ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    _ -> x : (ins n xs)

ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n == x of
    True -> x : xs
    _ -> x : (ins1 n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

main = hipSpec "ZenoComparsion6.hs" conf 3
  where conf = describe "Nats"
               [ var "x"         natType
               , var "y"         natType
               , var "z"         natType
               -- , var "a"         (undefined :: Bool)
               -- , var "b"         (undefined :: Bool)
               -- , var "c"         (undefined :: Bool)
               , var "xs"        listType
               , var "ys"        listType
               , var "zs"        listType
               -- , var "f"         (undefined :: Nat -> Nat)
               -- , var "g"         (undefined :: Nat -> Nat)
               -- , var "p"         (undefined :: Nat -> Bool)
               -- , var "q"         (undefined :: Nat -> Bool)
               -- , con "||"        (||)
               -- , con "[]"        ([]       :: [Nat])
               -- , con ":"         ((:)      :: Nat  -> [Nat] -> [Nat])
               -- , con "++"        ((++)     :: [Nat] -> [Nat] -> [Nat])
               -- , con "take"      (take :: Nat -> [Nat] -> [Nat])
               -- , con "count"     (count :: Nat -> [Nat] -> Nat)
               , con "elem"      (elem  :: Nat -> [Nat] -> Bool)
               -- , con "filter"    (filter :: (Nat -> Bool) -> [Nat] -> [Nat])
               -- , con "map"       (map :: (Nat -> Nat) -> [Nat] -> [Nat])
               -- , con "takeWhile" (takeWhile :: (Nat -> Bool) -> [Nat] -> [Nat])
               -- , con "dropWhile" (dropWhile :: (Nat -> Bool) -> [Nat] -> [Nat])
               -- , con "len"       (len :: [Nat] -> Nat)
               -- , con "rev"       (rev :: [Nat] -> [Nat])
               -- , con "ins"       (ins :: Nat -> [Nat] -> [Nat])
               -- , con "ins1"      (ins1 :: Nat -> [Nat] -> [Nat])
               -- , con "zip"       (zip :: [Nat] -> [Nat] -> [(Nat,Nat)])
               -- , con "zipConcat" (zipConcat :: Nat -> [Nat] -> [Nat] -> [(Nat,Nat)])
               -- , con "butlast"       (butlast       :: [Nat] -> [Nat])
               -- , con "butlastConcat" (butlastConcat :: [Nat] -> [Nat] -> [Nat])
               -- , con "sorted"     sorted
               -- , con "sort"       sort
               -- , con "last"       last
               -- , con "lastOfTwo"  lastOfTwo
               -- , con "delete"     delete
               -- , con "<="        (<=)
               -- , con "<"         (<)
               , con "=="        (==)
               -- , con "Z"         Z
               -- , con "S"         S
               -- , con "+"         (+)
               -- , con "-"         (-)
               -- , con "True"  True
               -- , con "False" False
               -- , con "min"       min
               -- , con "max"       max
               -- , con "height"    (height :: Tree Nat -> Nat)
               -- , con "mirror"    (mirror :: Tree Nat -> Tree Nat)
               ]
           where
             natType  = (error "Nat type" :: Nat)
             listType = (error "List type" :: [Nat])

             {-
prop_01 n xs
  = (take n xs ++ drop n xs =:= xs)

prop_02 n xs ys
  = (count n xs + count n ys =:= count n (xs ++ ys))

prop_03 n xs ys
  = proveBool (count n xs <= count n (xs ++ ys))

prop_04 n xs
  = (S (count n xs) =:= count n (n : xs))

{-
prop_05 n x xs
  = givenBool (n == x)
  $ (S (count n xs) =:= count n (x : xs))
  -}

prop_06 n m
  = (n - (n + m) =:= Z)

prop_07 n m
  = ((n + m) - n =:= m)

prop_08 k m n
  = ((k + m) - (k + n) =:= m - n)

prop_09 i j k
  = ((i - j) - k =:= i - (j + k))

prop_10 m
  = (m - m =:= Z)

prop_11 xs
  = (drop Z xs =:= xs)

prop_12 n f xs
  = (drop n (map f xs) =:= map f (drop n xs))

prop_13 n x xs
  = (drop (S n) (x : xs) =:= drop n xs)

prop_14 p xs ys
  = (filter p (xs ++ ys) =:= (filter p xs) ++ (filter p ys))

prop_15 x xs
  = (len (ins x xs) =:= S (len xs))

  {-
prop_16 (x :: Nat) xs
  = givenBool (xs == [])
  $ (last (x:xs) =:= x)
  -}

prop_17 n
  = (n <= Z =:= n == Z)

prop_18 i m
  = proveBool (i < S (i + m))

prop_19 n xs
  = (len (drop n xs) =:= len xs - n)

prop_20 xs
  = (len (sort xs) =:= len xs)

prop_21 n m
  = proveBool (n <= (n + m))

prop_22 a b c
  = (max (max a b) c =:= max a (max b c))

prop_23 a b
  = (max a b =:= max b a)

prop_24 a b
  = ((max a b) == a =:= b <= a)

prop_25 a b
  = ((max a b) == b =:= a <= b)

  {-
prop_26 x xs ys
  = givenBool (x `elem` xs)
  $ proveBool (x `elem` (xs ++ ys))

prop_27 x xs ys
  = givenBool (x `elem` ys)
  $ proveBool (x `elem` (xs ++ ys))
  -}

prop_28 x xs
  = proveBool (x `elem` (xs ++ [x]))
  -}

prop_29 :: Nat -> [Nat] -> Prop Bool
prop_29 x xs
  = proveBool (x `elem` ins1 x xs)

prop_30 :: Nat -> [Nat] -> Prop Bool
prop_30 x xs
  = proveBool (x `elem` ins x xs)

  {-
prop_31 a b c
  = (min (min a b) c =:= min a (min b c))

prop_32 a b
  = (min a b =:= min b a)

prop_33 a b
  = (min a b == a =:= a <= b)

prop_34 a b
  = (min a b == b =:= b <= a)

prop_35 xs
  = (dropWhile (\_ -> False) xs =:= xs)

prop_36 xs
  = (takeWhile (\_ -> True) xs =:= xs)

prop_37 x xs
  = proveBool (not (x `elem` delete x xs))

prop_38 n xs
  = (count n (xs ++ [n]) =:= S (count n xs))

prop_39 n x xs
  = (count n [x] + count n xs =:= count n (x:xs))

prop_40 xs
  = (take Z xs =:= [])

prop_41 n f xs
  = (take n (map f xs) =:= map f (take n xs))

prop_42 n x xs
  = (take (S n) (x:xs) =:= x : (take n xs))

prop_43 p xs
  = (takeWhile p xs ++ dropWhile p xs =:= xs)

prop_44 x xs ys
  = (zip (x:xs) ys =:= zipConcat x xs ys)

prop_45 x y xs ys
  = (zip (x:xs) (y:ys) =:= (x, y) : zip xs ys)

prop_46 xs
  = (zip [] xs =:= [])

  {-
prop_47 a
  = (height (mirror a) =:= height a)
  -}

  {-
prop_48 xs
  = given (xs == [] =:= False)
  $ (butlast xs ++ [last xs] =:= xs)
  -}

prop_49 xs ys
  = (butlast (xs ++ ys) =:= butlastConcat xs ys)

prop_50 :: [a] -> Prop [a]
prop_50 xs
  = (butlast xs =:= take (len xs - S Z) xs)

prop_51 xs x
  = (butlast (xs ++ [x]) =:= xs)

prop_52 n xs
  = (count n xs =:= count n (rev xs))

prop_53 n xs
  = (count n xs =:= count n (sort xs))

prop_54 n m
  = ((m + n) - n =:= m)

prop_55 n xs ys
  = (drop n (xs ++ ys) =:= drop n xs ++ drop (n - len xs) ys)

prop_56 n m xs
  = (drop n (drop m xs) =:= drop (n + m) xs)

prop_57 n m xs
  = (drop n (take m xs) =:= take (m - n) (drop n xs))

prop_58 n xs ys
  = (drop n (zip xs ys) =:= zip (drop n xs) (drop n ys))

  {-
prop_59 xs ys
  = givenBool (ys == [])
  $ (last (xs ++ ys) =:= last xs)

prop_60 xs ys
  = given (ys == [] =:= False)
  $ (last (xs ++ ys) =:= last ys)

  -}
prop_61 xs ys
  = (last (xs ++ ys) =:= lastOfTwo xs ys)

  {-
prop_62 xs x
  = given (xs == [] =:= False)
  $ (last (x:xs) =:= last xs)
  -}
{-
prop_63 n xs
  = givenBool (n < len xs)
  $ (last (drop n xs) =:= last xs)
  -}
prop_64 x xs
  = (last (xs ++ [x]) =:= x)

prop_65 i m =
  proveBool (i < S (m + i))

prop_66 :: (a -> Bool) -> [a] -> Prop Bool
prop_66 p xs
  = proveBool (len (filter p xs) <= len xs)

prop_67 :: [a] -> Prop Nat
prop_67 xs
  = (len (butlast xs) =:= len xs - S Z)

prop_68 :: Nat -> [Nat] -> Prop Bool
prop_68 n xs
  = proveBool (len (delete n xs) <= len xs)

prop_69 n m
  = proveBool (n <= (m + n))

  {-
prop_70 m n
  = givenBool (m <= n)
  $ proveBool (m <= S n)

prop_71 x y xs
  = given (x == y =:= False)
  $ (elem x (ins y xs) =:= elem x xs)
  -}

prop_72 i xs
  = (rev (drop i xs) =:= take (len xs - i) (rev xs))

prop_73 :: (a -> Bool) -> [a] -> Prop [a]
prop_73 p xs
  = (rev (filter p xs) =:= filter p (rev xs))

prop_74 i xs
  = (rev (take i xs) =:= drop (len xs - i) (rev xs))

prop_75 n m xs
  = (count n xs + count n [m] =:= count n (m : xs))

  {-
prop_76 n m xs
  = given (n == m =:= False)
  $ (count n (xs ++ [m]) =:= count n xs)


  prop_77 x xs
  = givenBool (sorted xs)
  $ proveBool (sorted (insort x xs))
  -}

prop_78 xs
  = proveBool (sorted (sort xs))

prop_79 m n k
  = ((S m - n) - S k =:= (m - n) - k)

prop_80 n xs ys
  = (take n (xs ++ ys) =:= take n xs ++ take (n - len xs) ys)

prop_81 n m xs {- ys -}
  = (take n (drop m xs) =:= drop m (take (n + m) xs))

prop_82 n xs ys
  = (take n (zip xs ys) =:= zip (take n xs) (take n ys))

prop_83 xs ys zs
  = (zip (xs ++ ys) zs =:=
           zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs))

prop_84 xs ys zs
  = (zip xs (ys ++ zs) =:=
           zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs)

prop_85 xs ys
  = (zip (rev xs) (rev ys) =:= rev (zip xs ys))

prop_01 :: Nat -> [a] -> Prop [a]
prop_02 :: Nat -> [Nat] -> [Nat] -> Prop Nat
prop_03 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_04 :: Nat -> [Nat] -> Prop Nat
prop_06 :: Nat -> Nat -> Prop Nat
prop_07 :: Nat -> Nat -> Prop Nat
prop_08 :: Nat -> Nat -> Nat -> Prop Nat
prop_09 :: Nat -> Nat -> Nat -> Prop Nat
prop_10 :: Nat -> Prop Nat
prop_11 :: [a] -> Prop [a]
prop_12 :: Nat -> (a1 -> a) -> [a1] -> Prop [a]
prop_13 :: Nat -> a -> [a] -> Prop [a]
prop_14 :: (a -> Bool) -> [a] -> [a] -> Prop [a]
prop_15 :: Nat -> [Nat] -> Prop Nat
prop_17 :: Nat -> Prop Bool
prop_18 :: Nat -> Nat -> Prop Bool
prop_19 :: Nat -> [a] -> Prop Nat
prop_20 :: [Nat] -> Prop Nat
prop_21 :: Nat -> Nat -> Prop Bool
prop_22 :: Nat -> Nat -> Nat -> Prop Nat
prop_23 :: Nat -> Nat -> Prop Nat
prop_24 :: Nat -> Nat -> Prop Bool
prop_25 :: Nat -> Nat -> Prop Bool
prop_28 :: Nat -> [Nat] -> Prop Bool
prop_31 :: Nat -> Nat -> Nat -> Prop Nat
prop_32 :: Nat -> Nat -> Prop Nat
prop_33 :: Nat -> Nat -> Prop Bool
prop_34 :: Nat -> Nat -> Prop Bool
prop_35 :: [a] -> Prop [a]
prop_36 :: [a] -> Prop [a]
prop_37 :: Nat -> [Nat] -> Prop Bool
prop_38 :: Nat -> [Nat] -> Prop Nat
prop_39 :: Nat -> Nat -> [Nat] -> Prop Nat
prop_40 :: [a] -> Prop [a]
prop_41 :: Nat -> (a1 -> a) -> [a1] -> Prop [a]
prop_42 :: Nat -> a -> [a] -> Prop [a]
prop_43 :: (a -> Bool) -> [a] -> Prop [a]
prop_44 :: a -> [a] -> [b] -> Prop [(a, b)]
prop_45 :: a -> b -> [a] -> [b] -> Prop [(a, b)]
prop_46 :: [b] -> Prop [(a, b)]
prop_49 :: [a] -> [a] -> Prop [a]
prop_51 :: [a] -> a -> Prop [a]
prop_52 :: Nat -> [Nat] -> Prop Nat
prop_53 :: Nat -> [Nat] -> Prop Nat
prop_54 :: Nat -> Nat -> Prop Nat
prop_55 :: Nat -> [a] -> [a] -> Prop [a]
prop_56 :: Nat -> Nat -> [a] -> Prop [a]
prop_57 :: Nat -> Nat -> [a] -> Prop [a]
prop_58 :: Nat -> [a] -> [b] -> Prop [(a, b)]
prop_61 :: [Nat] -> [Nat] -> Prop Nat
prop_64 :: Nat -> [Nat] -> Prop Nat
prop_65 :: Nat -> Nat -> Prop Bool
prop_69 :: Nat -> Nat -> Prop Bool
prop_72 :: Nat -> [a] -> Prop [a]
prop_74 :: Nat -> [a] -> Prop [a]
prop_75 :: Nat -> Nat -> [Nat] -> Prop Nat
prop_78 :: [Nat] -> Prop Bool
prop_79 :: Nat -> Nat -> Nat -> Prop Nat
prop_80 :: Nat -> [a] -> [a] -> Prop [a]
prop_81 :: Nat -> Nat -> [a] -> Prop [a]
prop_82 :: Nat -> [a] -> [b] -> Prop [(a, b)]
prop_83 :: [a] -> [a] -> [b] -> Prop [(a, b)]
prop_84 :: [a] -> [a1] -> [a1] -> Prop [(a, a1)]
prop_85 :: [a] -> [b] -> Prop [(a, b)]
-}
