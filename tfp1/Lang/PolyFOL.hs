{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell, ScopedTypeVariables #-}
{-

Type signatures and formulae have a list of top-level quantified
type variables. They have type * (or $tType in tff1).

Formula example:

    forall (a : *) (b : *)
    -- ^ type quantification
    forall (f : Fn(a,b)) (x : a) (xs : List(a))
    -- ^ (ordinary) value quantification
    map(a,b,f,cons(a,x,xs)) = cons(b,app(a,b,f,x),map(a,b,f,xs))

Type signature example:

    forall (a : *) (b : *)
    map : (Fn(a,b) * List(a)) -> List(b)

-}
module Lang.PolyFOL where

import Data.Generics.Geniplate

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Set (Set)
import qualified Data.Set as S

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Clauses.
--
-- The a type variable is used for many different identifiers:
-- * Quantified variables
-- * Type variables
-- * Function and predicate symbols (Nick: constants (or simply symbols))
-- * Type constructor symbols
data Clause a
    = SortSig
        { sig_id    :: a
        -- ^ Symbol this signature is for
        , sort_args :: Int
        -- ^ Number of kind arguments, see Note [Simple Kinded Sorts]
        }
    | TypeSig
        { sig_id :: a
        -- ^ Symbol this signature is for
        , ty_vars :: [a]
        -- ^ Type variables
        , sig_args :: [Type a]
        -- ^ Types of the arguments
        , sig_res :: Type a
        -- ^ Result type for this identifer
        }
    | Clause
        { cl_name :: Maybe Int
        -- ^ Name for this clause to get unsatisfiable cores
        , cl_type :: ClType
        -- ^ Axiom, conjecture...
        , ty_vars :: [a]
        -- ^ Top-level type variables
        , cl_formula :: Formula a
        -- ^ Formula in this clause
        }
    | Comment
        { comment :: String
        -- ^ A comment.
        }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data ClType
    = Axiom
    -- ^ Axioms, or definitions, or hypothesis or negated conjectures
    --   Is it important to distinguish between these?
    | Goal
    -- ^ Conjecture
  deriving (Eq,Ord,Show)

data Type a
    = TyCon a [Type a]
    | TyVar a
    | TType
    -- ^ The type of types
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Term operations
data TOp = Equal | Unequal
  deriving (Eq,Ord,Show)

-- | Formula operations
data FOp = And | Or | Implies | Equiv
  deriving (Eq,Ord,Show)

-- | Quantifier operations
data Q = Forall | Exists
  deriving (Eq,Ord,Show)

data Formula a
    = TOp TOp (Term a) (Term a)
    -- ^ Equality and inequality
    | FOp FOp (Formula a) (Formula a)
    -- ^ Logical connectives
    | Neg (Formula a)
    -- ^ Negation
    | Q Q a (Type a) (Formula a)
    -- ^ Quantification
    | Pred a [Formula a]
    -- ^ Predication
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

collectFOp :: Formula a -> Maybe (FOp,[Formula a])
collectFOp f0@(FOp op _ _) = Just (op,go f0)
  where
    go (FOp op' f1 f2) | op == op' = go f1 ++ go f2
    go f = [f]
collectFOp _              = Nothing

collectQ :: Formula a -> Maybe (Q,([(a,Type a)],Formula a))
collectQ f0@(Q q _ _ _) = Just (q,go f0)
  where
    go (Q q' x t f) | q == q' = let (xs,f') = go f
                                in  ((x,t):xs,f')
    go f = ([],f)
collectQ _             = Nothing

-- * Builders

infix 3 ===, =/=

(===),(=/=) :: Term a -> Term a -> Formula a
(===) = TOp Equal
(=/=) = TOp Unequal

infixr 2 /\
infixr 1 \/
infixr 0 ==>, ===>, <=>

(/\),(\/),(==>),(<=>) :: Formula a -> Formula a -> Formula a
(/\)  = FOp And
(\/)  = FOp Or
(==>) = FOp Implies
(<=>) = FOp Equiv

(===>) :: [Formula a] -> Formula a -> Formula a
[] ===> psi = psi
xs ===> psi = foldr1 (/\) xs ==> psi

forAll,exists :: a -> Type a -> Formula a -> Formula a
forAll = Q Forall
exists = Q Exists

forAlls,existss :: [(a,Type a)] -> Formula a -> Formula a
[forAlls,existss] = map (\ f xs phi -> foldr (uncurry f) phi xs) [forAll,exists]

-- | Terms.
data Term a
    = Apply a [Type a] [Term a]
    -- ^ Symbol applied to arguments (can be empty)
    | Var a
    -- ^ Quantified variable
    | Lit Integer
    -- ^ An integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

tmSubst :: forall a . Eq a => a -> Term a -> Term a -> Term a
tmSubst x tm = go
  where
    tr_tm :: (Term a -> Term a) -> Term a -> Term a
    tr_tm = $(genTransformBi 'tr_tm)

    go :: Term a -> Term a
    go = tr_tm $ \ tm0 -> case tm0 of
        Var y | x == y -> tm
        _              -> tm0

fmSubst :: forall a . Eq a => a -> Term a -> Formula a -> Formula a
fmSubst x = tr_fm . tmSubst x
  where
    tr_fm :: (Term a -> Term a) -> Formula a -> Formula a
    tr_fm = $(genTransformBi 'tr_fm)

clsDeps :: forall a . Ord a => [Clause a] -> (Set a,Set a)
clsDeps cls =
    (S.fromList [ tc | TyCon tc _ <- univ_ty cls ]
    ,S.fromList [ f | Apply f _ _ <- univ_tm cls ]
    )
  where
    univ_tm :: [Clause a] -> [Term a]
    univ_tm = $(genUniverseBi 'univ_tm)

    univ_ty :: [Clause a] -> [Type a]
    univ_ty = $(genUniverseBi 'univ_ty)

{-

Note [Simple Kinded Sorts] Every sort is simple kinded, and the
number of arguments is represented by an Int.

    0: *
    1: * -> *
    2: (* x *) -> *
    3: (* x * x *) -> *

Examples:

    Fn : (* x *) -> *
    List : * -> *

Reason:

In tff1, you cannot quantify over functions. Say you had

    data Sum k a b = Left (k a) | Right (k b)

Sum would get this type:

    tff(_, type,
        sum : (($tType > $tType) * $tType * $tType) > $tType
    ).

Then the type of the Left constructor would be:

    tff(_, type,
        left : !>[K : $tType > $tType,A : $tType,B : $tType] :
            K(A) > sum(K,A,B)
    ).

The quantification (k : * -> *) is not allowed.
This could be supported by defunctionalising the kind level too.

-}

