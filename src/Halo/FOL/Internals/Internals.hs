{-# LANGUAGE TemplateHaskell, RankNTypes, MultiParamTypeClasses #-}
module Halo.FOL.Internals.Internals where

import Data.Generics.Geniplate

-- Prefer to import Halo.FOL.Abstract or Halo.FOL.Operations than this file!

-- | Terms describing expressions, parameterised over
--   the variables a
--
--     v : the variables
--         This will typically be GHC's Var or String
--     q : the quantified variables
--         This will typically be GHC's Var or String
--
--  Note that other constants can be made by Fun and an empty list of
--  arguments (fun0 in Halo.FOL.Abstract)
data Term q v
    = Fun v [Term q v]
    | Ctor v [Term q v]
    | Skolem v
    | App (Term q v) (Term q v)
    | Proj Int v (Term q v)
    | Ptr v
    | QVar q
    | Prim Prim [Term q v]
    | Lit Integer
  deriving (Eq,Ord,Show)

-- | Primitive operations on int
data Prim = Add | Sub | Mul | Eq | Ne | Lt | Le | Ge | Gt | LiftBool
  deriving (Eq,Ord,Show)

-- | Predicates
data Pred = CF | Min | MinRec | IsType
  deriving (Eq,Ord,Show)

-- | Formulae
data Formula q v
    = Equal (Term q v) (Term q v)
    | Unequal (Term q v) (Term q v)
    | And [Formula q v]
    | Or  [Formula q v]
    | Implies (Formula q v) (Formula q v)
--  | Equiv   (Formula q v) (Formula q v)
    | Neg (Formula q v)
    | Forall [q] (Formula q v)
    | Exists [q] (Formula q v)
    | Pred Pred [Term q v]
  deriving (Eq,Ord,Show)

data ClType
    = Axiom | Lemma | Hypothesis | Definition
    | Conjecture | NegatedConjecture | Question
  deriving (Eq,Ord,Show)

data Clause q v
    = Clause String ClType (Formula q v)
    | Comment String
  deriving (Eq,Ord,Show)

-- These are defined here rather than in Operations to avoid orphan instances

instanceTransformBi [t| forall q v . (Term q v    ,Term q v    ) |]
instanceTransformBi [t| forall q v . (Term q v    ,Formula q v ) |]
instanceTransformBi [t| forall q v . (Formula q v ,Formula q v ) |]

instanceUniverseBi [t| forall q v . (Term q v   ,Term q v   ) |]
instanceUniverseBi [t| forall q v . (Formula q v,Term q v   ) |]
instanceUniverseBi [t| forall q v . (Formula q v,Formula q v) |]
instanceUniverseBi [t| forall q v . (Clause q v ,Formula q v) |]
instanceUniverseBi [t| forall q v . (Clause q v ,Term q v)    |]
