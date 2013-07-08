module BExp where

data Nat = Zero_nat
         | Suc Nat


data Ifex = Cif Bool
          | Vif Nat
          | If Ifex Ifex Ifex

data Boolex = Const Bool
            | Var Nat
            | Neg Boolex
            | And Boolex Boolex

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

