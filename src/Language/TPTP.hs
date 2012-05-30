module Language.TPTP where

newtype FunName = FunName { funName :: String } deriving (Eq,Ord)
newtype RelName = RelName { relName :: String } deriving (Eq,Ord)
newtype VarName = VarName { varName :: String } deriving (Eq,Ord)

instance Show FunName where show = funName
instance Show RelName where show = relName
instance Show VarName where show = varName

data Term = Fun FunName [Term]
          | Var VarName
  deriving (Eq,Ord,Show)

data EqOp = (:==) | (:!=)
  deriving (Eq,Ord,Show)

data BinOp = (:&) | (:|) | (:=>) | (:<=>)
  deriving (Eq,Ord,Show)

data Formula = EqOp Term EqOp Term
             | Rel RelName [Term]
             | Neg Formula
             | BinOp Formula BinOp Formula
             | Forall [VarName] Formula
             | Exists [VarName] Formula
  deriving (Eq,Ord,Show)

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

(===>) :: [Formula] -> Formula -> Formula
[]  ===> phi = phi
[x] ===> phi = x ==> phi
xs  ===> phi = foldr1 (/\) xs ==> phi


(===),(!=) :: Term -> Term -> Formula
(===) = \f g -> EqOp f (:==) g
(!=)  = \f g -> EqOp f (:!=) g

data Decl = Axiom      { declName :: String , declFormula :: Formula }
          | Conjecture { declName :: String , declFormula :: Formula }
          | Question   { declName :: String , declFormula :: Formula }
          | NegConj    { declName :: String , declFormula :: Formula }
          | Lemma      { declName :: String , declFormula :: Formula }
          | Hypothesis { declName :: String , declFormula :: Formula }
          | Definition { declName :: String , declFormula :: Formula }
  deriving (Eq,Ord,Show)

forall' :: [VarName] -> Formula -> Formula
forall' [] phi = phi
forall' xs phi = Forall xs phi

exists' :: [VarName] -> Formula -> Formula
exists' [] phi = phi
exists' xs phi = Exists xs phi
