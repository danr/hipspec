{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

{-- 
 This is an example about compiling expressions from the Isabelle
 tutorial "A Proof Assistant for Higher Order Logic", section
 3.3. Warning: This does not currently compile as we don't have
 Arbitrary instances etc for constructors which take functions as
 args. This is future work.   
--}

module Main where
import Prelude (Ord)
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
 
data Expr a b = Cex b
              | Vex a
              | Bex (b -> b -> b) (Expr a b) (Expr a b)
--              deriving (Eq, Ord, Typeable)

deriving instance (Eq b) => Eq (Expr a b)
deriving instance (Ord b) => Ord (Expr a b)
 
deriveEnumerable ''Expr
 
instance (Enumerable a) => (Enumerable b) => Arbitrary (Expr b a) where
        arbitrary = sized uniform
 
hd :: forall a . [a] -> a
hd (x : xs) = x
 
tl :: forall a . [a] -> [a]
tl [] = []
tl (x : xs) = xs
 
data Instr a b = Const b
               | Load a
               | Apply (b -> b -> b)
               deriving (Eq, Ord, Typeable)
 
deriveEnumerable ''Instr
 
instance (Enumerable a b) => Arbitrary (Instr b a) where
        arbitrary = sized uniform
 
exec :: forall a b . [Instr a b] -> (a -> b) -> [b] -> [b]
exec [] s vs = vs
exec (i : is) s vs
  = (case i of
         Const v -> exec is s (v : vs)
         Load a -> exec is s (s a : vs)
         Apply f -> exec is s (f (hd vs) (hd (tl vs)) : tl (tl vs)))
 
value :: forall a b . Expr a b -> (a -> b) -> b
value (Cex v) env = v
value (Vex a) env = env a
value (Bex f e1 e2) env = f (value e1 env) (value e2 env)
 
compile :: forall a b . Expr a b -> [Instr a b]
compile (Cex v) = [Const v]
compile (Vex a) = [Load a]
compile (Bex f e1 e2) = compile e2 ++ compile e1 ++ [Apply f]
main
  = hipSpec $( fileName )
      [vars ["a", "b", "c"] (Prelude.undefined :: [Instr A A]),
       vars ["a", "b", "c"] (Prelude.undefined :: [A]),
       vars ["a", "b", "c"] (Prelude.undefined :: Expr A A),
       vars ["a", "b", "c"] (Prelude.undefined :: A),
       vars ["a", "b", "c"] (Prelude.undefined :: (A -> A)),
       fun1 "Apply" (Apply :: (A -> A -> A) -> Instr A A),
       fun3 "Bex"
         (Bex :: (A -> A -> A) -> (Expr A A) -> (Expr A A) -> Expr A A),
       fun1 "Cex" (Cex :: A -> Expr A A),
       fun1 "Const" (Const :: A -> Instr A A),
       fun1 "Load" (Load :: A -> Instr A A),
       fun1 "Vex" (Vex :: A -> Expr A A),
       fun1 "compile" (compile :: Expr A A -> [Instr A A]),
       fun3 "exec" (exec :: [Instr A A] -> (A -> A) -> [A] -> [A]),
       fun1 "hd" (hd :: [A] -> A), fun1 "tl" (tl :: [A] -> [A]),
       fun2 "value" (value :: Expr A A -> (A -> A) -> A)]