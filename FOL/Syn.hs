-- (c) Dan Rosén 2012
module FOL.Syn where

import Control.Applicative
import Data.List

-- Constants and functions
newtype FunName = FunName { funName :: String } deriving (Eq,Ord)

-- Predicates and relations
newtype RelName = RelName { relName :: String } deriving (Eq,Ord)

-- Quantified Variables
newtype VarName = VarName { varName :: String } deriving (Eq,Ord)

instance Show FunName where show = funName
instance Show RelName where show = relName
instance Show VarName where show = varName

-- Terms
data Term = Fun FunName [Term]
          | FVar VarName
  deriving (Eq,Ord,Show)

-- Equality Operators
data EqOp = (:==) | (:!=)
  deriving (Eq,Ord,Show)

-- Binary Operators
data BinOp = (:&) | (:|) | (:=>) | (:<=>)
  deriving (Eq,Ord,Show)

-- Formulae
data Formula = EqOp Term EqOp Term
             | Rel RelName [Term]
             | Neg Formula
             | BinOp Formula BinOp Formula
             | Forall [VarName] Formula
             -- ^ Invariant : non-empty var list
             | Exists [VarName] Formula
             -- ^ Invariant : non-empty var list
  deriving (Eq,Ord,Show)

-- List of formulas
type Formulae = [Formula]

-- Utility functions to make formulae
mkBinOp :: BinOp -> Formula -> Formula -> Formula
mkBinOp op f g = BinOp f op g

infix 4 ===
infix 4 !=
infixr 3 &
infixr 3 :&
infixr 3 /\
infixr 2 \/
infixr 2 :|
infixl 1 ==>
infixl 1 :=>
infix  1 <=>

(==>),(&),(/\),(\/),(<=>) :: Formula -> Formula -> Formula
(==>) = mkBinOp (:=>)
(&)   = mkBinOp (:&)
(/\)  = mkBinOp (:&)
(\/)  = mkBinOp (:|)
(<=>) = mkBinOp (:<=>)

(===),(!=) :: Term -> Term -> Formula
(===) = \f g -> EqOp f (:==) g
(!=)  = \f g -> EqOp f (:!=) g

data DeclType = Axiom | Conjecture | Question | NegConj | Lemma | Hypothesis
  deriving (Eq,Ord,Show)

data FDecl = FDecl { declType :: DeclType
                   , declName :: String
                   , declFormula :: Formula
                   }
  deriving (Eq,Ord,Show)

forall' :: [VarName] -> Formula -> Formula
forall' [] phi = phi
forall' xs phi = Forall xs phi

exists' :: [VarName] -> Formula -> Formula
exists' [] phi = phi
exists' xs phi = Exists xs phi

{-
forallUnbound :: Formula -> Formula
forallUnbound = flip forall' <*> unbound

unbound :: Formula -> [VarName]
unbound (EqOp t1 _ t2) = unbTerm t1 ++ unbTerm t2
unbound (Rel _ ts) = concatMap unbTerm ts
unbound (Neg f) = unbound f
unbound (BinOp f1 _ f2) = unbound f1 ++ unbound f2
unbound (Forall bs f) = unbound f \\ bs   -- possibly incorrect, capture problem
unbound (Exists bs f) = unbound f \\ bs   -- possibly incorrect, capture problem

unbTerm :: Term -> [VarName]
unbTerm (FVar x) = [x]
unbTerm (Fun _ ts) = concatMap unbTerm ts
-}
