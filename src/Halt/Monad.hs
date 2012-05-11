{-# LANGUAGE NamedFieldPuns,
             GeneralizedNewtypeDeriving,
             FlexibleContexts,
             RecordWildCards
  #-}
module Halt.Monad where

import CoreSubst
import CoreSyn
import Id
import Name
import Outputable
import TyCon
import Unique

import Halt.Common
import Halt.Conf
import Halt.Constraints
import Halt.Data
import Halt.Utils

import qualified Data.Map as M
import Data.Map (Map)
import Data.List (delete,union)

import Control.Monad.Reader
import Control.Monad.Writer

-- Map associating each function/CAF with its arity
type ArityMap = Map Name Int

showArityMap :: ArityMap -> [String]
showArityMap m =
    [ showSDoc (ppr k) ++ "(" ++ show (getUnique k) ++ "):" ++ show v
    | (k,v) <- M.toList m ]

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

-- | Make the environment
mkEnv :: HaltConf -> [TyCon] -> [CoreBind] -> HaltEnv
mkEnv conf@(HaltConf{..}) ty_cons program =
  let -- Remove the unnecessary SCC information
      binds :: [(Var,CoreExpr)]
      binds = flattenBinds program

      -- Arity of each function (Arities from other modules are also needed)
      arities :: ArityMap
      arities = M.fromList $ [ (idName v,exprArity e) | (v,e) <- binds ]
                             ++ dataArities ty_cons

  in HaltEnv { arities = arities
             , fun     = error "initEnv: fun"
             , args    = []
             , quant   = []
             , constr  = noConstraints
             , conf    = conf
             }

runHaltM :: HaltEnv -> HaltM a -> (a,[String])
runHaltM env (HaltM m) = runWriter (m `runReaderT` env)

-- | The translation monad
newtype HaltM a = HaltM (ReaderT HaltEnv (Writer [String]) a)
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
