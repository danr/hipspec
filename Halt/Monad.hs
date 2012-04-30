{-# LANGUAGE NamedFieldPuns,
             GeneralizedNewtypeDeriving,
             FlexibleContexts
  #-}
module Halt.Monad where

import CoreSubst
import CoreSyn
import DataCon
import Name
import Outputable
import Var

import Halt.Util (showExpr)

import qualified Data.Map as M
import Data.Map (Map)
import Data.List (delete,union)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative

-- Map associating each function/CAF with its arity
type ArityMap = Map Name Int

-- The Environment
data HaltEnv
  = HaltEnv { arities  :: ArityMap
            -- ^ Arities of top level definitions
            , fun      :: Var
            -- ^ Current function
            , args     :: [CoreExpr]
            -- ^ Arguments to current function
            , quant    :: [Var]
            -- ^ Quantified variables
            , constr   :: [Constraint]
            -- ^ Constraints
            }


-- Pushes new quantified variables to the environment
pushQuant :: [Var] -> HaltEnv -> HaltEnv
pushQuant qs env = env { quant = qs `union` quant env }

-- Deletes a variable from the quantified list
delQuant :: Var -> HaltEnv -> HaltEnv
delQuant v env = env { quant = delete v (quant env) }

-- Pushes a new constraint to an environment
pushConstraint :: Constraint -> HaltEnv -> HaltEnv
pushConstraint c = pushConstraints [c]

-- Pushes many new constraints to an environment
pushConstraints :: [Constraint] -> HaltEnv -> HaltEnv
pushConstraints cs env = env { constr = cs ++ constr env }

-- Extends the arities
extendArities :: ArityMap -> HaltEnv -> HaltEnv
extendArities am env = env { arities = am `M.union` arities env }

-- Constraints from case expressions to results, under a substitution
data Constraint = CoreExpr :== Pattern
                | CoreExpr :/= Pattern

-- A pattern
data Pattern = Pattern DataCon [CoreExpr]

trPattern :: Pattern -> CoreExpr
trPattern (Pattern data_con as) = foldl App (Var (dataConWorkId data_con)) as

instance Show Pattern where
  show = showExpr . trPattern

instance Show Constraint where
  show (e :== p) = showExpr e ++ " :== " ++ show p
  show (e :/= p) = showExpr e ++ " :/= " ++ show p

substConstr :: Subst -> Constraint -> Constraint
substConstr s (e :== p) = substExpr (text "substConstr") s e :== substPattern s p
substConstr s (e :/= p) = substExpr (text "substConstr") s e :/= substPattern s p

substPattern :: Subst -> Pattern -> Pattern
substPattern s (Pattern data_con as)
    = Pattern data_con (map (substExpr (text "substPattern") s) as)

-- | The empty constraints
noConstraints :: [Constraint]
noConstraints = []

-- | The initial environment
initEnv :: ArityMap -> HaltEnv
initEnv am
    = HaltEnv { arities = am
              , fun     = error "initEnv: fun"
              , args    = []
              , quant   = []
              , constr  = noConstraints
              }

-- | The translation monad
newtype HaltM a
    = HaltM { runHaltM :: ReaderT HaltEnv (Writer [String]) a }
  deriving (Applicative,Monad,Functor
           ,MonadReader HaltEnv
           ,MonadWriter [String])

substContext :: Subst -> HaltEnv -> HaltEnv
substContext s env = env
    { args = map (substExpr (text "substContext:args") s) (args env)
    , constr = map (substConstr s) (constr env)
    }

-- | Write a debug message
write :: MonadWriter [String] m => String -> m ()
write = tell . return

