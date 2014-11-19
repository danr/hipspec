module Eval where

data Nat = S Nat | Z

index :: [a] -> Nat -> a
index (x:xs) Z     = x
index (x:xs) (S n) = index xs n

data Expr
    = App2 Nat Expr Expr
    | Case Nat Expr Expr
    | Cons Expr Expr
    | Nil
    | Var Nat

eval :: [Expr] -> [[Nat]] -> Expr -> [Nat]
eval prog env e0 = case e0 of
    App2 f e1 e2 -> eval prog (eval prog env e1:eval prog env e2:env) (prog `index` f)
    Case x nl cn -> case env `index` x of
        []     -> eval prog env nl
        (x:xs) -> eval prog ([x]:xs:env) cn
--    Cons hd tl -> case eval prog env hd of
--        []  -> Z:eval prog env tl
--        y:_ -> y:eval prog env tl
--    Nil -> []
--    Var x -> env `index` x
