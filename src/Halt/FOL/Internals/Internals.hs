{-# LANGUAGE DeriveDataTypeable,ScopedTypeVariables #-}
module Halt.FOL.Internals.Internals where

import Halt.PrimCon
import Data.Data

-- Only Halt.FOL.Abstract and Halt.FOL.Linearise should use this module!

-- | Terms describing expressions, parameterised over
--   the variables a
--
--     v : the variables
--         This will typically be GHC's Var or String
--     q : the quantified variables
--         This will typically be GHC's Var or String
--
--  Note that other prims can be made by Fun and an empty list of arguments
data Term q v
    = Fun v [Term q v]
    | Con v [Term q v]
    | App (Term q v) (Term q v)
    | Proj Int v (Term q v)
    | Ptr v
    | QVar q
    | Constant PrimCon
  deriving (Eq,Ord,Show,Data,Typeable)

data Formula q v
    = Equal (Term q v) (Term q v)
    | Unequal (Term q v) (Term q v)
    | And [Formula q v]
    | Or  [Formula q v]
    | Implies (Formula q v) (Formula q v)
    | Neg (Formula q v)
    | Forall [q] (Formula q v)
    | Exists [q] (Formula q v)
    | CF (Term q v)
    | Min (Term q v)
  deriving (Eq,Ord,Show,Data,Typeable)

data ClType = Axiom | Lemma | Hypothesis | Definition
            | Conjecture | NegatedConjecture | Question
  deriving (Eq,Ord,Show,Data,Typeable)

data Clause q v = Clause ClType String (Formula q v)
                | Comment String
  deriving (Eq,Ord,Show,Data,Typeable)
