{-# LANGUAGE DeriveDataTypeable #-}
module Assoc where

import HipSpec
import Control.Monad

data Expr
    = Add Expr Expr
    | Mul Expr Expr
    | Var
  deriving (Typeable,Eq,Ord,Show)

instance Names Expr where
  names _ = ["u","v","w"]

instance Arbitrary Expr where
  arbitrary = sized arb
   where
    arb s = frequency
      [ (1,return Var)
      , (s,liftM2 Add (arb s2) (arb s2))
      , (s,liftM2 Mul (arb s2) (arb s2))
      ]
     where s2 = s`div`2

assoc :: Expr -> Expr
assoc (Add (Add e1 e2) e3) = assoc (Add e1 (Add e2 e3))
assoc (Add e1 e2)          = Add (assoc e1) (assoc e2)
assoc (Mul (Mul e1 e2) e3) = assoc (Mul e1 (Mul e2 e3))
assoc (Mul e1 e2)          = Mul (assoc e1) (assoc e2)
assoc Var                  = Var

isRight :: Expr -> Bool
isRight (Add e1 e2) = not (isAdd e1) && isRight e1 && isRight e2
isRight (Mul e1 e2) = not (isMul e1) && isRight e1 && isRight e2
isRight Var         = True

sameTop Add{} Add{} = True
sameTop Mul{} Mul{} = True
sameTop Var   Var   = True
sameTop _     _     = False

isAdd Add{} = True
isAdd _ = False

isMul Mul{} = True
isMul _ = False

isVar Var{} = True
isVar _ = False

prop_same_top u = sameTop u (assoc u) =:= True

prop_assoc_help u = (isAdd u,isMul u,isVar u,isRight (assoc u)) =:= (isAdd (assoc u),isMul (assoc u),isVar (assoc u),True)

