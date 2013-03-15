{-# LANGUAGE TemplateHaskell, RankNTypes, MultiParamTypeClasses, FlexibleInstances #-}
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
--     t : the types
--         Will at some point be GHC's Type... or some other representation
--         (and later String)
--
--  Note that other constants can be made by Fun and an empty list of
--  arguments (fun0 in Halo.FOL.Abstract)
data Term q v t
    = Fun v [Term q v t]
    | Ctor v [Term q v t]
    | Skolem v t
    | App t (Term q v t) (Term q v t)
    | Proj Int v (Term q v t)
    | Ptr v t
    | QVar q
    | Bottom t
    | Lit Integer
    | Prim Prim [Term q v t]
  deriving (Eq,Ord,Show)

-- | Primitive operations on int
data Prim = Add | Sub | Mul | Eq | Ne | Lt | Le | Ge | Gt | LiftBool
  deriving (Eq,Ord,Show)

-- | Formulae
data Formula q v t
    = Equal (Term q v t) (Term q v t)
    | Unequal (Term q v t) (Term q v t)
    | And [Formula q v t]
    | Or  [Formula q v t]
    | Implies (Formula q v t) (Formula q v t)
    | Equiv   (Formula q v t) (Formula q v t)
    | Neg (Formula q v t)
    | Forall [(q,t)] (Formula q v t)
    | Exists [(q,t)] (Formula q v t)
    | Total t (Term q v t)
  deriving (Eq,Ord,Show)

data ClType
    = Axiom | Lemma | Hypothesis | Definition
    | Conjecture | NegatedConjecture | Question
  deriving (Eq,Ord,Show)

data TyThing v t
    = AFun v
    | AnApp t
    | ACtor v
    | ASkolem v
    | AProj Int v
    | APtr v
    | ABottom t
  deriving (Eq,Ord,Show)

data Clause q v t
    = Clause (Maybe Int) ClType (Formula q v t)
    | TypeSig (TyThing v t) [t] t
    -- ^ v has type t1 -> .. -> tn -> t
    --   where t1..tn is in the list
    | SortSig t
    -- ^ t is a sort
    | TotalSig t
    | Comment String
  deriving (Eq,Ord,Show)

-- These are defined here rather than in Operations to avoid orphan instances

instanceTransformBi [t| forall q v t . (Term q v t    ,Term q v t    ) |]
instanceTransformBi [t| forall q v t . (Term q v t    ,Formula q v t ) |]
instanceTransformBi [t| forall q v t . (Formula q v t ,Formula q v t ) |]

instanceUniverseBi [t| forall q v t . (Term q v t     ,Term q v t   ) |]
instanceUniverseBi [t| forall q v t . (Formula q v t  ,Term q v t   ) |]
instanceUniverseBi [t| forall q v t . (Formula q v t  ,Formula q v t) |]
instanceUniverseBi [t| forall q v t . ([Formula q v t],Term q v t)    |]
instanceUniverseBi [t| forall q v t . (Clause q v t   ,Formula q v t) |]
instanceUniverseBi [t| forall q v t . ([Clause q v t] ,Formula q v t) |]
instanceUniverseBi [t| forall q v t . (Clause q v t   ,Term q v t)    |]
instanceUniverseBi [t| forall q v t . ([Clause q v t] ,Term q v t)    |]

