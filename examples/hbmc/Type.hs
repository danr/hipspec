module Type where

import HipSpec

data Nat = S Nat | Z
  deriving Show

index :: [a] -> Nat -> Maybe a
index (x:xs) Z     = Just x
index (x:xs) (S n) = index xs n
index []     _     = Nothing

data Expr = App Expr Expr Ty | Lam Expr | Var Nat

instance Show Expr where
  show = showExpr []

showExpr env (Var v)     = case env `index` v of Just x -> x; Nothing -> "?"
showExpr env (App a b t) = "(" ++ showExpr env a ++ " " ++ showExpr env b ++ ")"
showExpr env (Lam e)     = "(\\" ++ v ++ " -> " ++ showExpr (v:env) e ++ ")"
 where
  v = head [ x | x <- vars, x `notElem` env ]
  vars = [ "x", "y", "z", "v", "w" ] ++ [ "x" ++ show i | i <- [1..] ]

data Ty = Ty :-> Ty | A | B | C
  deriving (Eq,Show)

infixr :->

tc :: [Ty] -> Expr -> Ty -> Bool
tc env e0 t0 = case e0 of
    App f x t1   -> tc env f (t1 :-> t0) && tc env x t1
    Var x        -> case env `index` x of
                        Just tx -> tx == t0
                        Nothing -> False
    Lam e        -> case t0 of
        t1 :-> t2 -> tc (t1:env) e t2
        _         -> False

prop_I e = tc [] e (A :-> A) =:= False

prop_K e = tc [] e (A :-> B :-> A) =:= False

prop_K1 e = tc [] e (A :-> B :-> B) =:= False

prop_D e = tc [] e ((A :-> B) :-> (A :-> B)) =:= False

prop_N e = tc [] e (A :-> (A :-> A) :-> A) =:= False

prop_W e = tc [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False

prop_M e = tc [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

prop_B e = tc [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False
