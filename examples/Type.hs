module Type where

data Nat = S Nat | Z

index :: [a] -> Nat -> a
index (x:xs) Z     = x
index (x:xs) (S n) = index xs n

data Expr = App Expr Expr Ty | Lam Expr | Var Nat

data Ty = Ty :-> Ty | A | B
  deriving Eq

tc :: [Ty] -> Expr -> Ty -> Bool
tc env e0 t0 = case e0 of
    App e1 e2 t2 -> tc env e1 (t2 :-> t0) && tc env e2 t2
    Var x        -> (env `index` x) == t0
    Lam e        -> case t0 of
        t1 :-> t2 -> tc (t1:env) e t2
        _         -> False

