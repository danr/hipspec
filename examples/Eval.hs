module Eval where

data Nat = S Nat | Z
  deriving Show

index :: [a] -> Nat -> a
index (x:xs) Z     = x
index (x:xs) (S n) = index xs n

data Expr
    = App2 Nat Expr Expr
    | Cons Expr Expr
    | Case Nat Expr Expr
    | Nil
    | Var Nat
  deriving Show

eval :: [Expr] -> [[Nat]] -> Expr -> [Nat]
eval prog env e0 = case e0 of
    App2 f e1 e2 -> eval prog (eval prog env e1:eval prog env e2:env) (prog `index` f)
    Cons hd tl -> zhead (eval prog env hd):eval prog env tl
    Case x nl cn -> case env `index` x of
        []     -> eval prog env nl
        (x:xs) -> eval prog ([x]:xs:env) cn
    Nil -> []
    Var x -> env `index` x

zhead []    = Z
zhead (x:_) = x
