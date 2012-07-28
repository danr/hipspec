{-# LANGUAGE PatternGuards, FlexibleContexts #-}
-- (c) Dan Rosén 2012
module Halo.FOL.Abstract
    ( Term', Formula', Clause', StrClause

    , apply, con

    , fun, fun0
    , ctor, ctor0

    , app, apps
    , proj
    , qvar
    , skolem
    , ptr

    , isAtomic
    , simpleCNF
    , splitFormula, splitFormulae

    , (===), (=/=)
    , (==>), (===>)
    , (/\), ands
    , (\/), ors
    , neg
    , forall', exists'
    , foralls

    , min', minrec
    , cf

    , Formula
    , Term
    , ClType
    , Clause
    , clause
    , comment
    , namedClause
    , clauseSplit

    , axiom, lemma, hypothesis, definition
    , conjecture, negatedConjecture, question

    , axioms, definitions
    ) where

import Var
import Id

import Halo.FOL.Internals.Internals
import Halo.FOL.Operations

import Control.Applicative ((<*>))
import Data.Generics.Geniplate

type Term'    = Term    Var Var
type Formula' = Formula Var Var
type Clause'  = Clause  Var Var

type StrClause  = Clause String String

comment :: String -> Clause q v
comment = Comment

clause :: ClType -> Formula q v -> Clause q v
clause = Clause "x"

namedClause :: String -> ClType -> Formula q v -> Clause q v
namedClause = Clause

clauseSplit :: ClType -> Formula q v -> [Clause q v]
clauseSplit cl_type = map (clause cl_type) . splitFormula

-- | Figure out if this var is one of the primitive constants, or if
--   it is a data constructor or a function, and make a term accordingly.
apply :: Var -> [Term q Var] -> Term q Var
apply x as
    | isId x && isConLikeId x = Ctor x as
    | otherwise               = Fun x as

-- | Make a term of this primitive constant, constructor or CAF.
con :: Var -> Term q Var
con x = apply x []

fun :: v -> [Term q v] -> Term q v
fun = Fun

fun0 :: v -> Term q v
fun0 a = Fun a []

ctor :: v -> [Term q v] -> Term q v
ctor = Ctor

ctor0 :: v -> Term q v
ctor0 a = Ctor a []

app :: Term q v -> Term q v -> Term q v
app = App

apps :: Term q v -> [Term q v] -> Term q v
apps = foldl App

proj :: Int -> v -> Term q v -> Term q v
proj = Proj

qvar :: q -> Term q v
qvar = QVar

skolem :: v -> Term q v
skolem = Skolem

ptr :: v -> Term q v
ptr = Ptr

infix 4 ===
infix 4 =/=

(===),(=/=) :: Term q v -> Term q v -> Formula q v
(===) = Equal
(=/=) = Unequal

infixl 1 ==>
infixl 1 ===>

-- | Implication
(==>) :: Formula q v -> Formula q v -> Formula q v
(==>) = Implies

-- | [l1,..,ln] ===> r means
--   l1 /\ .. /\ ln ==> r1
(===>) :: [Formula q v] -> Formula q v -> Formula q v
[]  ===> f = f
phi ===> f = ands phi ==> f

infixr 2 \/
infixr 3 /\

(\/),(/\) :: Formula q v -> Formula q v -> Formula q v
a \/ b = ors [a,b]
a /\ b = ands [a,b]

ands :: [Formula q v] -> Formula q v
ands []  = error "ands: Empty list"
ands [f] = f
ands fs  = And (concatMap flattenAnd fs)

flattenAnd :: Formula q v -> [Formula q v]
flattenAnd (And fs) = concatMap flattenAnd fs
flattenAnd f        = [f]

ors :: [Formula q v] -> Formula q v
ors []  = error "ors: Empty list"
ors [f] = f
ors fs  = Or (concatMap flattenOr fs)

flattenOr :: Formula q v -> [Formula q v]
flattenOr (Or fs) = concatMap flattenOr fs
flattenOr f       = [f]

neg :: Formula q v -> Formula q v
neg (Neg f)         = f
neg (Equal t1 t2)   = Unequal t1 t2
neg (Unequal t1 t2) = Equal t1 t2
neg (And fs)        = Or (map neg fs)
neg (Or fs)         = And (map neg fs)
neg (Implies f1 f2) = neg f2 `Implies` neg f1
neg (Forall as f)   = Exists as (neg f)
neg (Exists as f)   = Forall as (neg f)
neg f               = Neg f

forall' :: [q] -> Formula q v -> Formula q v
forall' [] f = f
forall' as f = Forall as f

exists' :: [q] -> Formula q v -> Formula q v
exists' [] f = f
exists' as f = Exists as f

foralls :: (UniverseBi (Formula q v) (Formula q v)
           ,UniverseBi (Formula q v) (Term q v)
           ,Ord q)
        => Formula q v -> Formula q v
foralls = flip forall' <*> allQuant

min' :: Term q v -> Formula q v
min' = Min

minrec :: Term q v -> Formula q v
minrec = MinRec

cf :: Term q v -> Formula q v
cf = CF

type Atomic q v = Formula q v

isAtomic :: Formula q v -> Bool
isAtomic f = case f of
    Equal{}     -> True
    Unequal{}   -> True
    Or{}        -> False
    And{}       -> False
    Implies{}   -> False
    (Neg Neg{}) -> False
    (Neg x)     -> isAtomic x
    Forall{}    -> False
    Exists{}    -> False
    CF{}        -> True
    Min{}       -> True
    MinRec{}    -> True

-- | Can this formula be written simply in CNF?
simpleCNF :: Formula q v -> Maybe [Atomic q v]
simpleCNF (Forall _ f)              = simpleCNF f
simpleCNF (Implies f1 f2)           = simpleCNF (neg f1 \/ f2)
simpleCNF (Or fs) | all isAtomic fs = Just fs
simpleCNF f       | isAtomic f      = Just [f]
simpleCNF _                         = Nothing

-- | Split the conjuncts of a formula over many formulae,
--   distributing any foralls over them
splitFormula :: Formula q v -> [Formula q v]
splitFormula (Forall vs fs) = map (forall' vs) (splitFormula fs)
splitFormula (And fs)       = concatMap splitFormula fs
splitFormula f              = [f]

-- | Split conjuncts in many formulae at once
splitFormulae :: [Formula q v] -> [Formula q v]
splitFormulae = concatMap splitFormula


-- Clause types

axiom :: ClType
axiom = Axiom

lemma :: ClType
lemma = Lemma

hypothesis :: ClType
hypothesis = Hypothesis

definition :: ClType
definition = Definition

conjecture :: ClType
conjecture = Conjecture

negatedConjecture :: ClType
negatedConjecture = NegatedConjecture

question :: ClType
question = Question

-- Making many clauses

axioms :: [Formula q v] -> [Clause q v]
axioms = map (clause axiom)

definitions :: [Formula q v] -> [Clause q v]
definitions = map (clause definition)
