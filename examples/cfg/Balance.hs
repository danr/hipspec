{-# LANGUAGE DeriveDataTypeable #-}
module Balance where

import Prelude hiding ((++),(+))
import Control.Monad
import Test.QuickCheck hiding ((==>))
import Data.Typeable
import Tip.DSL

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

data S = Two A A
  deriving (Typeable,Eq,Ord,Show)

data A = One A | Last
  deriving (Typeable,Eq,Ord,Show)

data Tok = X | Y
  deriving (Typeable,Eq,Ord,Show)

lin :: S -> [Tok]
lin (Two a b) = linA a ++ linA b

linA :: A -> [Tok]
linA (One a)   = [X] ++ linA a ++ [X]
linA Last      = [Y]

{-
bal a & bal b ==> lin (Two s t) = a ++ b
! (bal a & bal b ==> lin (One s) = a ++ b)
-}

data Nat = S Nat | Z deriving (Eq,Show,Typeable,Ord)

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

lemma2 v w s t = linA v ++ s =:= linA w ++ t ==> (v,s) =:= (w,t)

-- lemma v w s t = [C] ++ lin v ++ [D] ++ s =:= [C] ++ lin w ++ [D] ++ t ==> (v,s) =:= (w,t)
-- lemma2 v w s t = lin v ++ s =:= lin w ++ t ==> (v,s) =:= (w,t)
-- lemma3 v w s t = lin v ++ [D] ++ lin s =:= [C] ++ lin w ++ [D] ++ lin t ==> (v,s) =:= (w,t)

-- lemma4 v w s t = v ++ [D] ++ lin s =:= w ++ [D] ++ lin t ==> (v,s) =:= (w,t)

unambig u v = lin u =:= lin v ==> u =:= v

-- injR u v w = v ++ u =:= w ++ u ==> v =:= w
-- inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w
-- injL u v w = u ++ v =:= u ++ w ==> v =:= w

{-
inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w

injL u v w = u ++ v =:= u ++ w ==> v =:= w

injR v w u = v ++ u =:= w ++ u ==> v =:= w
-}


instance Arbitrary S where
  arbitrary = liftM2 Two arbitrary arbitrary

instance Arbitrary A where
  arbitrary = sized arb
   where
    arb s = frequency
      [ (1,return Last)
      , (s,liftM One (arb (s-1)))
--      , (s,liftM2 Two (arb s2) (arb s2))
      ]
     where
      s2 = s `div` 2

instance Arbitrary Tok where
  arbitrary = elements [X,Y]


instance Arbitrary Nat where
    arbitrary =
        let nats = iterate S Z
        in  (nats !!) `fmap` choose (0,5)

