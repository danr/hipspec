-- (c) Dan Rosén 2012
module FOL.Abstract
{-       ( Term
       , fun,app,con,proj,qvar,ptr
       , Formula
       , (===),(=/=)
       , (==>),(===>)
       , (\/),(/\)
       , ands,ors
       , neg
       , forall',exists'
       , minPred, cfPred
       , ClType(..)
       , Clause(..)
       , simpleCNF
       ) -} where

-- | Terms describing expressions, parameterised on the type of the
--   variables. This will typically be GHC Vars and later strings.
data Term a
    = Fun a [Term a]
    | App (Term a) (Term a)
    | Proj Int a (Term a)
    | Ptr a
    | QVar a
  deriving (Eq,Ord,Show)

fun :: a -> [Term a] -> Term a
fun = Fun

con :: a -> Term a
con a = Fun a []

app :: Term a -> Term a -> Term a
app = App

apps :: Term a -> [Term a] -> Term a
apps = foldl App

proj :: Int -> a -> Term a -> Term a
proj = Proj

qvar :: a -> Term a
qvar = QVar

ptr :: a -> Term a
ptr = Ptr

data Formula a
    = Equal (Term a) (Term a)
    | Unequal (Term a) (Term a)
    | And [Formula a]
    | Or  [Formula a]
    | Implies (Formula a) (Formula a)
    | Neg (Formula a)
    | Forall [a] (Formula a)
    | Exists [a] (Formula a)
    | CF (Term a)
    | Min (Term a)
  deriving (Eq,Ord,Show)

type Literal a = Formula a

isLiteral :: Formula a -> Bool
isLiteral f = case f of
    Equal{}     -> True
    Unequal{}   -> True
    Or{}        -> False
    And{}       -> False
    Implies{}   -> False
    (Neg Neg{}) -> False
    (Neg x)     -> isLiteral x
    Forall{}    -> False
    Exists{}    -> False
    CF{}        -> True
    Min{}       -> True

-- | Can this formula be written simply in CNF?
simpleCNF :: Formula a -> Maybe [Literal a]
simpleCNF (Forall _ f)               = simpleCNF f
simpleCNF (Implies f1 f2)            = simpleCNF (neg f1 \/ f2)
simpleCNF (Or fs) | all isLiteral fs = Just fs
simpleCNF f       | isLiteral f      = Just [f]
simpleCNF _                          = Nothing

infix 4 ===
infix 4 =/=

(===),(=/=) :: Term a -> Term a -> Formula a
(===) = Equal
(=/=) = Unequal

infixl 1 ==>
infixl 1 ===>

-- | Implication
(==>) :: Formula a -> Formula a -> Formula a
(==>) = Implies

-- | [l1,..,ln] ===> r means
--   l1 /\ .. /\ ln ==> r1
(===>) :: [Formula a] -> Formula a -> Formula a
[]  ===> f = f
phi ===> f = ands phi ==> f

infixr 2 \/
infixr 3 /\

(\/),(/\) :: Formula a -> Formula a -> Formula a
a \/ b = ors [a,b]
a /\ b = ands [a,b]

ands :: [Formula a] -> Formula a
ands []  = error "ands: Empty list"
ands [f] = f
ands fs  = And (concatMap flattenAnd fs)

flattenAnd :: Formula a -> [Formula a]
flattenAnd (And fs) = concatMap flattenAnd fs
flattenAnd f        = [f]

ors :: [Formula a] -> Formula a
ors []  = error "ors: Empty list"
ors [f] = f
ors fs  = Or (concatMap flattenOr fs)

flattenOr :: Formula a -> [Formula a]
flattenOr (Or fs) = concatMap flattenOr fs
flattenOr f       = [f]

neg :: Formula a -> Formula a
neg (Neg f)         = f
neg (Equal t1 t2)   = Unequal t1 t2
neg (Unequal t1 t2) = Equal t1 t2
neg (And fs)        = Or (map neg fs)
neg (Or fs)         = And (map neg fs)
neg (Implies f1 f2) = neg f2 `Implies` neg f1
neg (Forall as f)   = Exists as (neg f)
neg (Exists as f)   = Forall as (neg f)
neg f               = Neg f

forall' :: [a] -> Formula a -> Formula a
forall' [] f = f
forall' as f = Forall as f

exists' :: [a] -> Formula a -> Formula a
exists' [] f = f
exists' as f = Exists as f

minPred :: Term a -> Formula a
minPred = Min

cfPred :: Term a -> Formula a
cfPred = CF

data ClType = Axiom | Lemma | Hypothesis | Definition
            | Conjecture | NegatedConjecture | Question
  deriving (Eq,Ord,Show)

data Clause a = Clause ClType String (Formula a)
              | Comment String
  deriving (Eq,Ord,Show)

