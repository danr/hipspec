{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module HipSpec.Lang.PolyFOL.Types where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

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

data Trigger a
    = TySymb a
    -- ^ Needs to be first!
    | Symb a
    | Source
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

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
    | DataDecl [DataDecl a b] (Formula a b)
    -- ^ One or many data declarations for SMT data types,
    --   or a formula if it is not supported
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data DataDecl a b = Data a [Type a b] [(a,[(a,Type a b)])]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Terms.
data Term a b
    = Apply a [Type a b] [Term a b]
    -- ^ Symbol applied to arguments (can be empty)
    | Var b
    -- ^ Quantified variable
    | Lit Integer
    -- ^ An integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

