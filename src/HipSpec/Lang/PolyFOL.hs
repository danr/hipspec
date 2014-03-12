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
module HipSpec.Lang.PolyFOL where

import Data.Generics.Geniplate
import Data.Generics.Genifunctors

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor

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
data Clause a b
    = SortSig
        { sig_id    :: a
        -- ^ Symbol this signature is for
        , sort_args :: Int
        -- ^ Number of kind arguments, see Note [Simple Kinded Sorts]
        }
    | TypeSig
        { sig_id :: a
        -- ^ Symbol this signature is for
        , ty_vars :: [b]
        -- ^ Type variables
        , sig_args :: [Type a b]
        -- ^ Types of the arguments
        , sig_res :: Type a b
        -- ^ Result type for this identifer
        }
    | Clause
        { cl_name :: Maybe Int
        -- ^ Name for this clause to get unsatisfiable cores
        , cl_ty_triggers :: [Trigger a]
        -- ^ What things trigger the instantiation of this clause?
        --   For function definitions, the function causes it
        --   For data type-related definitions, the type constructor and
        --   its data constructors do
        , cl_type :: ClType
        -- ^ Axiom, conjecture...
        , ty_vars :: [b]
        -- ^ Top-level type variables
        , cl_formula :: Formula a b
        -- ^ Formula in this clause
        }
    | Comment
        { comment :: String
        -- ^ A comment.
        }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Bifunctor Clause     where bimap      = bimapDefault
instance Bifoldable Clause    where bifoldMap  = bifoldMapDefault
instance Bitraversable Clause where bitraverse = $(genTraverse ''Clause)

data Trigger a
    = TySymb a
    -- ^ Needs to be first!
    | Symb a
    | Source
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

isTySymb :: Trigger a -> Bool
isTySymb TySymb{} = True
isTySymb _        = False

data ClType
    = Axiom
    -- ^ Axioms, or definitions, or hypothesis or negated conjectures
    --   Is it important to distinguish between these?
    | Goal
    -- ^ Conjecture
  deriving (Eq,Ord,Show)

data Type a b
    = TyCon a [Type a b]
    | TyVar b
    | TType
    -- ^ The type of types
    | Integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Bifunctor Type     where bimap      = bimapDefault
instance Bifoldable Type    where bifoldMap  = bifoldMapDefault
instance Bitraversable Type where bitraverse = $(genTraverse ''Type)

-- | Term operations
data TOp = Equal | Unequal
  deriving (Eq,Ord,Show)

-- | Formula operations
data FOp = And | Or | Implies | Equiv
  deriving (Eq,Ord,Show)

-- | Quantifier operations
data Q = Forall | Exists
  deriving (Eq,Ord,Show)

data Formula a b
    = TOp TOp (Term a b) (Term a b)
    -- ^ Equality and inequality
    | FOp FOp (Formula a b) (Formula a b)
    -- ^ Logical connectives
    | Neg (Formula a b)
    -- ^ Negation
    | Q Q b (Type a b) (Formula a b)
    -- ^ Quantification
{-
    | Pred a [Formula a b]
    -- ^ Predication
-}
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

collectFOp :: Formula a b -> Maybe (FOp,[Formula a b])
collectFOp f0@(FOp op _ _) = Just (op,go f0)
  where
    go (FOp op' f1 f2) | op == op' = go f1 ++ go f2
    go f = [f]
collectFOp _              = Nothing

collectQ :: Formula a b -> Maybe (Q,([(b,Type a b)],Formula a b))
collectQ f0@(Q q _ _ _) = Just (q,go f0)
  where
    go (Q q' x t f) | q == q' = let (xs,f') = go f
                                in  ((x,t):xs,f')
    go f = ([],f)
collectQ _             = Nothing

-- * Builders

infix 3 ===, =/=

(===),(=/=) :: Term a b -> Term a b -> Formula a b
(===) = TOp Equal
(=/=) = TOp Unequal

infixr 2 /\
infixr 1 \/
infixr 0 ==>, ===>, <=>

(/\),(\/),(==>),(<=>) :: Formula a b -> Formula a b -> Formula a b
(/\)  = FOp And
(\/)  = FOp Or
(==>) = FOp Implies
(<=>) = FOp Equiv

(===>) :: [Formula a b] -> Formula a b -> Formula a b
[] ===> psi = psi
xs ===> psi = foldr1 (/\) xs ==> psi

forAll,exists :: b -> Type a b -> Formula a b -> Formula a b
forAll = Q Forall
exists = Q Exists

forAlls,existss :: [(b,Type a b)] -> Formula a b -> Formula a b
[forAlls,existss] = map (\ f xs phi -> foldr (uncurry f) phi xs) [forAll,exists]

-- | Terms.
data Term a b
    = Apply a [Type a b] [Term a b]
    -- ^ Symbol applied to arguments (can be empty)
    | Var b
    -- ^ Quantified variable
    | Lit Integer
    -- ^ An integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

topTmSubst :: Eq b => b -> Term a b -> Term a b -> Term a b
topTmSubst x tm tm0 = case tm0 of
    Var y | x == y -> tm
    _              -> tm0

tmSubst :: forall a b . Eq b => b -> Term a b -> Term a b -> Term a b
tmSubst x tm = tr_tm (topTmSubst x tm)
  where
    tr_tm :: (Term a b -> Term a b) -> Term a b -> Term a b
    tr_tm = $(genTransformBi 'tr_tm)

fmSubst :: forall a b . Eq b => b -> Term a b -> Formula a b -> Formula a b
fmSubst x tm = tr_fm (topTmSubst x tm)
  where
    tr_fm :: (Term a b -> Term a b) -> Formula a b -> Formula a b
    tr_fm = $(genTransformBi 'tr_fm)

topTySubst :: Eq b => b -> Type a b -> Type a b -> Type a b
topTySubst a ty ty0 = case ty0 of
    TyVar b | a == b -> ty
    _                -> ty0

fmInst :: forall a b . Eq b => b -> Type a b -> Formula a b -> Formula a b
fmInst a ty = tr_ty (topTySubst a ty)
  where
    tr_ty :: (Type a b -> Type a b) -> Formula a b -> Formula a b
    tr_ty = $(genTransformBi 'tr_ty)

tySubst :: forall a b . Eq b => b -> Type a b -> Type a b -> Type a b
tySubst a ty = tr_ty (topTySubst a ty)
  where
    tr_ty :: (Type a b -> Type a b) -> Type a b -> Type a b
    tr_ty = $(genTransformBi 'tr_ty)

fmInsts :: Eq b => [(b,Type a b)] -> Formula a b -> Formula a b
fmInsts xs phi = foldr (uncurry fmInst) phi xs

tySubsts :: Eq b => [(b,Type a b)] -> Type a b -> Type a b
tySubsts xs phi = foldr (uncurry tySubst) phi xs

clsDeps :: forall a b . Ord a => [Clause a b] -> (Set a,Set a)
clsDeps cls =
    (S.fromList [ tc | TyCon tc _ <- concatMap clTyUniv cls ]
    ,S.fromList [ f | Apply f _ _ <- concatMap clTmUniv cls ]
    )

clTmUniv :: Clause a b -> [Term a b]
clTmUniv = $(genUniverseBi 'clTmUniv)

clTyUniv :: Clause a b -> [Type a b]
clTyUniv = $(genUniverseBi 'clTyUniv)

fmMod :: (a -> [Type a b] -> Type c b)
      -> (a -> [Type a b] -> [Term c b] -> Term c b)
      -> Formula a b -> Formula c b
fmMod f g = fmg
  where
    fmg fm0 = case fm0 of
        TOp op tm1 tm2 -> TOp op (tmg tm1) (tmg tm2)
        FOp op fm1 fm2 -> FOp op (fmg fm1) (fmg fm2)
        Neg fm         -> Neg (fmg fm)
        Q q b ty fm    -> Q q b (tyg ty) (fmg fm)

    tmg tm0 = case tm0 of
        Apply x ts tms -> g x ts (map tmg tms)
        Var x          -> Var x
        Lit i          -> Lit i

    tyg = tyMod f

tyMod :: (a -> [Type a b] -> Type c b) -> Type a b -> Type c b
tyMod f ty0 = case ty0 of
    TyCon x ts -> f x ts
    TyVar x    -> TyVar x
    TType      -> TType
    Integer    -> Integer


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

