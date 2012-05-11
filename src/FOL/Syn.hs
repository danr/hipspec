-- (c) Dan Rosén 2012
module FOL.Syn where


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

neg :: Formula -> Formula
neg (EqOp t1 (:==) t2) = EqOp t1 (:!=) t2
neg (EqOp t1 (:!=) t2) = EqOp t1 (:==) t2
neg phi                = Neg phi

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

data DeclType = CNF
              | Axiom | Conjecture | NegConj | Question
              | Lemma | Hypothesis | Definition
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

