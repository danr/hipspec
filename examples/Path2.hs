-- Michal's encoding whatsisdoodle.

{-# LANGUAGE DeriveDataTypeable, GeneralizedNewtypeDeriving, CPP #-}
module Path2 where

import Test.QuickCheck hiding ((==>), Prop)
import QuickSpec hiding (Prop)
import Data.List hiding ((++), map)
import Data.Typeable
import HipSpec
import Prelude hiding ((++), (&&), map)
import qualified Data.Maybe

data Dir = L | R | N deriving ( Show, Eq, Typeable, Ord )

instance Arbitrary Dir where
  arbitrary = elements [L,R,N]

type Path = [Dir]

data Bit = O | I deriving ( Show, Eq, Typeable, Ord )

instance Arbitrary Bit where
  arbitrary = elements [O,I]

toBit N = Nothing
toBit L = Just O
toBit R = Just I

naive_fst :: Path -> [Bit]
naive_fst p = catMaybes (map toBit p)

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = f x:map f xs

{-# NOINLINE plus #-}
plus :: Integer -> Integer -> Integer
plus x y = x + y

ns :: [Dir] -> Integer
ns (N:xs) = 1 `plus` ns xs
ns (_:xs) = ns xs
ns [] = 0

catMaybes :: [Maybe a] -> [a]
catMaybes [] = []
catMaybes (Nothing:xs) = catMaybes xs
catMaybes (Just x:xs) = x:catMaybes xs

False && x = False
True && x = x

data Paths = Paths { left, right :: Path } deriving ( Show, Eq, Ord, Typeable )

instance Arbitrary Paths where
  arbitrary =
    do p0 <- arbitrary
       p1 <- arbitrary
       p2 <- arbitrary
       elements
         [ Paths p0 (p0 ++ [N] ++ p1)
         , Paths (p0 ++ [N] ++ p1) p0
         , Paths (p0 ++ [L] ++ p1) (p0 ++ [R] ++ p2)
         , Paths (p0 ++ [R] ++ p1) (p0 ++ [L] ++ p2)
         ]         

  shrink (Paths p1 p2) =
    filter (ok . removeCommon) 
    [ Paths (drop i p1) (drop i p2)
    | i <- [1..length p1 `min` length p2]
    ] ++
    [ Paths p1' p2
    | p1' <- shrink p1
    ] ++
    [ Paths p1 p2'
    | p2' <- shrink p2
    ]
   where
    removeCommon (Paths (x:xs) (y:ys)) | x == y = removeCommon (Paths xs ys)
    removeCommon p                              = p
   
    ok (Paths []    (N:_)) = True
    ok (Paths (N:_) [])    = True
    ok (Paths (L:_) (R:_)) = True
    ok (Paths (R:_) (L:_)) = True
    ok _                   = False

-- One argument is prefix of the other one
(=<|>=) :: [Bit] -> [Bit] -> Bool
[]    =<|>= q     = True
p     =<|>= []    = True
(a:p) =<|>= (b:q) = a ==== b && (p =<|>= q)
  where
    I ==== I = True
    O ==== O = True
    _ ==== _ = False

(++) :: [a] -> [a] -> [a]
[] ++ xs = xs
(x:xs) ++ ys = x:(xs++ys)

-- prop_lemma1 :: Path -> Path -> Path -> Prop Integer
-- prop_lemma1 p0 p1 p2 =
--   ns (p0 ++ p1) =:= ns (p0 ++ p2) ==> ns p1 =:= ns p2

-- prop_lemma2 :: Path -> Path -> Path -> Prop [Bit]
-- prop_lemma2 p0 p1 p2 =
--   naive_fst p1 =:= naive_fst p2 ==> naive_fst (p0 ++ p1) =:= naive_fst (p0 ++ p2)

prop_lemma :: Path -> Prop Bool
prop_lemma p = (ns p >= 0) =:= True

prop_1, prop_2 :: Path -> Path -> Prop Bool
prop_3, prop_4 :: Path -> Path -> Path -> Prop Bool

#define soundNaive(p0, p1) let { (q1, n1) = naive (p0); (q2, n2) = naive (p1); {-# INLINE naive #-}; naive p = (naive_fst p, ns p) } in n1 =:= n2 ==> (q1 =<|>= q2) =:= False

prop_1 p0 p1 = soundNaive(p0, p0 ++ [N] ++ p1)
prop_2 p0 p1 = soundNaive(p0 ++ [N] ++ p1, p0)
prop_3 p0 p1 p2 = soundNaive(p0 ++ [L] ++ p1, p0 ++ [R] ++ p2)
prop_4 p0 p1 p2 = soundNaive(p0 ++ [R] ++ p1, p0 ++ [L] ++ p2)

{-
sig :: Signature
sig =
  signature {
    instances = [
      names (NamesFor ["p"] :: NamesFor Path),
      baseTypeNames ["ps"] (undefined :: Paths),
      baseTypeNames ["d"] (undefined :: Dir),
      baseTypeNames ["b"] (undefined :: Bit) ],

    constants = [
      constant "[]" ([] :: [A]),
      constant ":" ((:) :: A -> [A] -> [A]),
      constant "++" ((++) :: [A] -> [A] -> [A]),
      constant "fst" (fst :: (A, B) -> A),
      constant "snd" (snd :: (A, B) -> B),
      constant "==" ((==) :: Integer -> Integer -> Bool),
      constant "=<|>=" ((=<|>=) :: [Bit] -> [Bit] -> Bool),
--      constant "/=<|>=" ((\x y -> not (x =<|>= y)) :: [Bit] -> [Bit] -> Bool),
      constant "True" True,
      constant "False" False,
      constant "||" (||),
      constant "not" not,
      constant "+" ((+) :: Integer -> Integer -> Integer),
      constant "0" (0 :: Integer),
      constant "1" (1 :: Integer),
      constant "N" N,
      constant "L" L,
      constant "R" R,
      constant "O" O,
      constant "I" I,
      constant "naive_q" (fst . naive),
      constant "naive_n" (snd . naive),
      constant "left" left,
      constant "right" right ]}

--main = quickSpecWithBackground bg sig
main = quickSpec sig
-}