module Expr where

import HipPrelude
import Prelude (Bool(..),Eq,Show)

-- Expressions with Nats ------------------------------------------------------

data Expr = Add Expr Expr
          | Mul Expr Expr
          | IsZero Expr
          | Val Nat
  deriving (Eq,Show)

data Nat = Z | S Nat deriving (Eq,Show)

mirror :: Expr -> Expr
mirror (Add e1 e2) = Add (mirror e2) (mirror e1)
mirror (Mul e1 e2) = Mul (mirror e2) (mirror e1)
mirror (IsZero e)  = IsZero (mirror e)
mirror e           = e

prop_mirror :: Expr -> Prop Expr
prop_mirror e = e =:= mirror (mirror e)

plus x Z     = x
plus x (S y) = S (plus x y)

size :: Expr -> Nat
size (Add e1 e2) = size e1 `plus` size e2
size (Mul e1 e2) = size e1 `plus` size e2
size (IsZero e)  = size e
size (Val _)     = S Z

times x Z     = Z
times x (S y) = (x `times` y) `plus` x

eval :: Expr -> Nat
eval (Add e1 e2) = eval e1 `plus` eval e2
eval (Mul e1 e2) = eval e1 `times` eval e2
eval (IsZero e) = case eval e of
                    Z -> S Z
                    _ -> Z
eval (Val n) = n

-- These probably need assoc and identity lemmas
prop_mirror_size :: Expr -> Prop Nat
prop_mirror_size e = size e =:= size (mirror e)

prop_mirror_eval :: Expr -> Prop Nat
prop_mirror_eval e = eval e =:= eval (mirror e)

-- Expressions on Bools -------------------------------------------------------

data BoolExpr = BoolExpr :&: BoolExpr | Value Bool

True  && x = x
False && _ = False

True  &&& True = True
_     &&& _    = False

boolEval :: BoolExpr -> Bool
boolEval (e1 :&: e2) = boolEval e1 && boolEval e2
boolEval (Value b)   = b

boolEval' :: BoolExpr -> Bool
boolEval' (e1 :&: e2) = boolEval' e1 &&& boolEval' e2
boolEval' (Value b)   = b

boolMirror :: BoolExpr -> BoolExpr
boolMirror (e1 :&: e2) = boolMirror e2 :&: boolMirror e1
boolMirror (Value b)   = Value b

prop_boolMirror_boolEval :: BoolExpr -> Prop Bool
prop_boolMirror_boolEval e = boolEval (boolMirror e) =:= boolEval e

prop_boolMirror_boolEval' :: BoolExpr -> Prop Bool
prop_boolMirror_boolEval' e = boolEval' (boolMirror e) =:= boolEval' e

prop_boolEval_boolEval' :: Prop (BoolExpr -> Bool)
prop_boolEval_boolEval' = boolEval =:= boolEval

prop_boolMirror_boolMirror :: BoolExpr -> Prop BoolExpr
prop_boolMirror_boolMirror e = boolMirror (boolMirror e) =:= e

-- FV -------------------------------------------------------------------------

data Lam = Var Nat | Lam :@ Lam | Abs Nat Lam

otherwise = True

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

mem :: Nat -> [Nat] -> Bool
mem x (y:ys) | x == y    = True
             | otherwise = x `mem` ys
mem x [] = False

union (x:xs) ys | x `mem` ys = union xs ys
                | otherwise  = x:union xs ys
union []     ys              = ys

delete u (x:xs) | x == u    = delete u xs
                | otherwise = x : delete u xs
delete u []                 = []

freeVars :: Lam -> [Nat]
freeVars (Var x)    = [x]
freeVars (e1 :@ e2) = freeVars e1 `union` freeVars e2
freeVars (Abs x e)  = delete x (freeVars e)

boolOr True  x = True
boolOr False x = x

boolNot True = False
boolNot False = False

boolAnd True  x = x
boolAnd False x = False

boolEq True True = True
boolEq False False = True
boolEq x y = False

freeIn :: Nat -> Lam -> Bool
v `freeIn` e = go e []
  where
    go :: Lam -> [Nat] -> Bool
    go (Var x)    env = v == x `boolAnd` boolNot (v `mem` env)
    go (e1 :@ e2) env = go e1 env `boolOr` go e2 env
    go (Abs x e)  env = go e (x:env)

prop_free :: Lam -> Nat -> Prop Bool
prop_free e v = v `mem` freeVars e =:= v `freeIn` e
