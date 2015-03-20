{-# LANGUAGE DeriveDataTypeable #-}
module Dyck where

import Prelude hiding ((++),(+))
import Control.Monad
import Test.QuickCheck hiding ((==>))
import Data.Typeable
import Tip.DSL

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

data S = Two S S | One S | Last
  deriving (Typeable,Eq,Ord,Show)

data Tok = C | D
  deriving (Typeable,Eq,Ord,Show)

lin :: S -> [Tok]
lin (Two a b) = [C] ++ lin a ++ [D] ++ lin b
lin (One a)   = [C] ++ lin a ++ [D]
lin Last      = [C,D]

{-
bal a & bal b ==> lin (Two s t) = a ++ b
! (bal a & bal b ==> lin (One s) = a ++ b)
-}

data Nat = S Nat | Z deriving (Eq,Show,Typeable,Ord)

bal :: Nat -> [Tok] -> Bool
bal n     (C:xs) = bal (S n) xs
bal (S n) (D:xs) = bal n xs
bal Z     []     = True
bal _     _      = False

{-
valleys :: Nat -> [Tok] -> Nat
valleys Z     (C:xs) = S (valleys (S Z) xs)
valleys m     (C:xs) = valleys (S m) xs
valleys (S n) (D:xs) = valleys n xs
valleys Z     []     = S Z
valleys _     _      = Z
-}

valleys :: Nat -> [Tok] -> Nat
valleys n     (C:xs) = valleys (S n) xs
valleys (S n) (D:xs) = case n of
                         Z -> S r
                         _ -> r
                      where r = valleys n xs
valleys _     _      = Z

gt :: Nat -> Nat -> Bool
Z   `gt` _ = False
S{} `gt` Z = True
S x `gt` S y = x `gt` y

-- prop_val a b c = valleys Z (lin (Two a b)) `gt` valleys Z (lin (One c)) =:= True

{-
bal_prop2 xs ys = bal Z xs =:= True
              ==> bal Z ys =:= True
              ==> bal Z (xs ++ ys) =:= True

bal_prop3 n m xs ys = bal n xs =:= True
                  ==> bal m ys =:= True
                  ==> bal (n + m) (xs ++ ys) =:= True
                  -}

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

lemma v w s t = [C] ++ lin v ++ [D] ++ s =:= [C] ++ lin w ++ [D] ++ t ==> (v,s) =:= (w,t)
-- lemma2 v w s t = lin v ++ s =:= lin w ++ t ==> (v,s) =:= (w,t)
lemma3 v w s t = lin v ++ [D] ++ lin s =:= [C] ++ lin w ++ [D] ++ lin t ==> (v,s) =:= (w,t)

lemma4 v w s t = v ++ [D] ++ lin s =:= w ++ [D] ++ lin t ==> (v,s) =:= (w,t)

unambig u v = lin u =:= lin v ==> u =:= v

injR u v w = v ++ u =:= w ++ u ==> v =:= w
inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w
injL u v w = u ++ v =:= u ++ w ==> v =:= w

{-
inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w

injL u v w = u ++ v =:= u ++ w ==> v =:= w

injR v w u = v ++ u =:= w ++ u ==> v =:= w
-}


instance Arbitrary S where
  arbitrary = sized arb
   where
    arb s = frequency
      [ (1,return Last)
      , (s,liftM One (arb (s-1)))
      , (s,liftM2 Two (arb s2) (arb s2))
      ]
     where
      s2 = s `div` 2

instance Arbitrary Tok where
  arbitrary = elements [C,D]


instance Arbitrary Nat where
    arbitrary =
        let nats = iterate S Z
        in  (nats !!) `fmap` choose (0,5)

