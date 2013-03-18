{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}
module Main where
import Prelude (Ord,Show)
import Prelude
       ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**), (>>=),
        (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
        error, id, return, not, fst, snd, map, filter, concat, concatMap,
        reverse, zip, null, takeWhile, dropWhile, all, any, Integer,
        negate, abs, divMod, String, Bool(True, False),
        Maybe(Nothing, Just))
import qualified Prelude
import HipSpec
import HipSpec.Prelude
import Data.Typeable
import Test.Feat
 
deriveEnumerable ''A
 
data Nat = Zero_nat
         | Suc Nat
         deriving (Eq, Ord, Typeable,Show)
 
deriveEnumerable ''Nat
 
instance Arbitrary Nat where
        arbitrary = sized uniform

instance CoArbitrary Nat where
  coarbitrary = coarbitraryShow
 
data Ifex = Cif Bool
          | Vif Nat
          | If Ifex Ifex Ifex
          deriving (Eq, Ord, Typeable)
 
deriveEnumerable ''Ifex
 
instance Arbitrary Ifex where
        arbitrary = sized uniform
 
data Boolex = Const Bool
            | Var Nat
            | Neg Boolex
            | And Boolex Boolex
            deriving (Eq, Ord, Typeable)
 
deriveEnumerable ''Boolex
 
instance Arbitrary Boolex where
        arbitrary = sized uniform
 
valif :: Ifex -> (Nat -> Bool) -> Bool
valif (Cif b) env = b
valif (Vif x) env = env x
valif (If b t e) env
  = (if valif b env then valif t env else valif e env)
 
value :: Boolex -> (Nat -> Bool) -> Bool
value (Const b) env = b
value (Var x) env = env x
value (Neg b) env = not (value b env)
value (And b c) env = value b env && value c env
 
bool2if :: Boolex -> Ifex
bool2if (Const b) = Cif b
bool2if (Var x) = Vif x
bool2if (Neg b) = If (bool2if b) (Cif False) (Cif True)
bool2if (And b c) = If (bool2if b) (bool2if c) (Cif False)
main
  = hipSpec $( fileName )
      [vars ["a", "b", "c"] (Prelude.undefined :: Bool),
       vars ["a", "b", "c"] (Prelude.undefined :: Boolex),
       vars ["a", "b", "c"] (Prelude.undefined :: Ifex),
       vars ["a", "b", "c"] (Prelude.undefined :: (Nat -> Bool)),
       fun2 "And" (And :: Boolex -> Boolex -> Boolex),
       fun1 "Cif" (Cif :: Bool -> Ifex),
       fun1 "Const" (Const :: Bool -> Boolex),
       fun3 "If" (If :: Ifex -> Ifex -> Ifex -> Ifex),
       fun1 "Neg" (Neg :: Boolex -> Boolex),
       fun1 "Suc" (Suc :: Nat -> Nat), 
       fun1 "Var" (Var :: Nat -> Boolex),
       fun1 "Vif" (Vif :: Nat -> Ifex), 
       fun0 "Zero_nat" (Zero_nat :: Nat),
       fun1 "bool2if" (bool2if :: Boolex -> Ifex),
       fun2 "valif" (valif :: Ifex -> (Nat -> Bool) -> Bool),
       fun2 "value" (value :: Boolex -> (Nat -> Bool) -> Bool)]
