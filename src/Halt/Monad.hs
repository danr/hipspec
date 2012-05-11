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

import Halt.Common
import Halt.Utils (showExpr)
import Halt.Conf
import Halt.Names

import qualified Data.Map as M
import Data.Map (Map)
import Data.List (delete,union)

import Control.Monad.Reader
import Control.Monad.Writer

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
              , conf     :: HaltConf
              -- ^ Configuration
              , names    :: Names
              -- ^ Names of constants UNR/BAD/Bottom
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
data Constraint = Equality   CoreExpr DataCon [CoreExpr]
                | Inequality CoreExpr DataCon

instance Show Constraint where
  show (Equality   e _dc _bs) = showExpr e ++ " == fix constraint show instance" -- ++ show p
  show (Inequality e _dc)     = showExpr e ++ " /= fix constraint show instance" -- ++ show p

substConstr :: Subst -> Constraint -> Constraint
substConstr s (Equality e dc bs) = Equality (substExpr (text "substConstr") s e) dc
                                            (map (substExpr (text "substConstr") s) bs)
substConstr s (Inequality e dc)  = Inequality (substExpr (text "substConstr") s e) dc

-- | The empty constraints
noConstraints :: [Constraint]
noConstraints = []

-- | The initial environment
initEnv :: Names -> HaltConf -> ArityMap -> HaltEnv
initEnv names conf am
    = HaltEnv { arities = am
              , fun     = error "initEnv: fun"
              , args    = []
              , quant   = []
              , constr  = noConstraints
              , conf    = conf
              , names   = names
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

getNameOf :: NamedConstant -> HaltM Name
getNameOf nt = namedName nt <$> asks names

getIdOf :: NamedConstant -> HaltM Id
getIdOf nt = namedId nt <$> asks names

getConOf :: NamedConstant -> HaltM DataCon
getConOf nt = namedCon nt <$> asks names
