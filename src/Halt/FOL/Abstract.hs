{-# LANGUAGE PatternGuards #-}
-- (c) Dan Rosén 2012
module Halt.FOL.Abstract
       (VarTerm,VarFormula,VarClause
       ,AxTerm,AxFormula,AxClause
       ,StrClause

       ,apply,con

       ,fun,fun0
       ,ctor,ctor0

       ,constant
       ,app,apps
       ,proj
       ,qvar
       ,ptr

       ,isLiteral
       ,simpleCNF

       ,(===),(=/=)
       ,(==>),(===>)
       ,(/\),ands
       ,(\/),ors
       ,neg
       ,forall',exists'

       ,min'
       ,cf

       ,Formula
       ,Term
       ,ClType(..)
       ,Clause(..)
       ) where

import Halt.FOL.Internals.Internals
import Halt.PrimCon

import Var
import Id

type VarTerm    = Term    Var Var
type VarFormula = Formula Var Var
type VarClause  = Clause  Var Var
type AxTerm     = Term    Int Var
type AxFormula  = Formula Int Var
type AxClause   = Clause  Int Var

type StrClause  = Clause String String

-- | Figure out if this var is one of the primitive constants, or if
--   it is a data constructor or a function, and make a term accordingly.
apply :: Var -> [Term q Var] -> Term q Var
apply x as
    | Just c <- lookup x primCons = apps (Constant c) as
    | isConLikeId x               = Ctor x as
    | otherwise                   = Fun x as
  where
    primCons = [(primId c,c) | c <- [minBound..maxBound]]

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

constant :: PrimCon -> Term q v
constant = Constant

app :: Term q v -> Term q v -> Term q v
app = App

apps :: Term q v -> [Term q v] -> Term q v
apps = foldl App

proj :: Int -> v -> Term q v -> Term q v
proj = Proj

qvar :: q -> Term q v
qvar = QVar

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

min' :: Term q v -> Formula q v
min' = Min

cf :: Term q v -> Formula q v
cf = CF

type Literal q v = Formula q v

isLiteral :: Formula q v -> Bool
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
simpleCNF :: Formula q v -> Maybe [Literal q v]
simpleCNF (Forall _ f)               = simpleCNF f
simpleCNF (Implies f1 f2)            = simpleCNF (neg f1 \/ f2)
simpleCNF (Or fs) | all isLiteral fs = Just fs
simpleCNF f       | isLiteral f      = Just [f]
simpleCNF _                          = Nothing
