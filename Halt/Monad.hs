{-# LANGUAGE NamedFieldPuns,
             GeneralizedNewtypeDeriving,
             FlexibleContexts
  #-}
module Halt.Monad where

import PprCore

import CoreSyn
import Var
import DataCon
import Outputable
import CoreSubst

import FOL.Syn hiding ((:==))

import qualified Data.Map as M
import Data.Map (Map)
import Data.List (delete,union)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative

-- Map associating each function/CAF with its arity
type ArityMap = Map Var Int

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
            -- , subs     :: Subs
            -- ^ Substitutions
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

-- -- Sets the current substitutions
-- extendSubs :: Subs -> HaltEnv -> HaltEnv
-- extendSubs s env = env { subs = s `M.union` subs env }

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
    = HaltM { runHaltM :: ReaderT HaltEnv (WriterT [String] (State Int)) a }
  deriving (Applicative,Monad,Functor
           ,MonadReader HaltEnv
           ,MonadWriter [String]
           ,MonadState Int)

substContext :: Subst -> HaltEnv -> HaltEnv
substContext s env = env
    { args = map (substExpr (text "substContext:args") s) (args env)
    , constr = map (substConstr s) (constr env)
    }

-- | Write a debug message
write :: MonadWriter [String] m => String -> m ()
write = tell . return

-- | Monad used when translating expressions : now new formulae can
--   appear because of local case and let
type ExprHaltM a = WriterT [Formula] HaltM a

showExpr :: CoreExpr -> String
showExpr = showSDoc . pprCoreExpr

getLabel :: (MonadState Int m) => m Int
getLabel = do { x <- get ; modify succ ; return x }

