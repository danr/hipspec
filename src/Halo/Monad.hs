{-# LANGUAGE NamedFieldPuns,
             GeneralizedNewtypeDeriving,
             FlexibleContexts,
             RecordWildCards
  #-}
module Halo.Monad where

import CoreSubst
import CoreSyn
import Id
import Name
import Outputable
import TyCon
import Unique
import VarSet

import Halo.Util
import Halo.Conf
import Halo.Constraints
import Halo.Data
import Halo.Shared

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.List (delete,union)

import Control.Monad.RWS

-- Map associating each function/CAF with its arity
type ArityMap = Map Name Int

showArityMap :: ArityMap -> [String]
showArityMap m =
    [ showSDoc (ppr k) ++ "(" ++ show (getUnique k) ++ "):" ++ show v
    | (k,v) <- M.toList m ]

-- The Environment
data HaloEnv
    = HaloEnv { arities     :: ArityMap
              -- ^ Arities of top level definitions
              , current_fun :: Var
              -- ^ Current function
              , args        :: [CoreExpr]
              -- ^ Arguments to current function
              , quant       :: [Var]
              -- ^ Quantified variables
              , constr      :: [Constraint]
              -- ^ Constraints
              , conf        :: HaloConf
              -- ^ Configuration
              }

-- Pushes new quantified variables to the environment
pushQuant :: [Var] -> HaloEnv -> HaloEnv
pushQuant qs env = env { quant = qs `union` quant env }

-- Deletes a variable from the quantified list
delQuant :: Var -> HaloEnv -> HaloEnv
delQuant v env = env { quant = delete v (quant env) }

-- Pushes a new constraint to an environment
pushConstraint :: Constraint -> HaloEnv -> HaloEnv
pushConstraint c = pushConstraints [c]

-- Pushes many new constraints to an environment
pushConstraints :: [Constraint] -> HaloEnv -> HaloEnv
pushConstraints cs env = env { constr = cs ++ constr env }

-- Extends the arities
extendArities :: ArityMap -> HaloEnv -> HaloEnv
extendArities am env = env { arities = am `M.union` arities env }

-- | Make the environment
mkEnv :: HaloConf -> [TyCon] -> [CoreBind] -> HaloEnv
mkEnv conf@HaloConf{..} ty_cons program =
  let -- Remove the unnecessary SCC information
      binds :: [(Var,CoreExpr)]
      binds = flattenBinds program

      -- Arity of each function (Arities from other modules are also needed)
      arities :: ArityMap
      arities = M.fromList $ [ (idName v,exprArity e) | (v,e) <- binds ]
                             ++ dataArities ty_cons

  in HaloEnv { arities     = arities
             , current_fun = error "initEnv: current_fun"
             , args        = []
             , quant       = []
             , constr      = noConstraints
             , conf        = conf
             }

runHaloM :: HaloEnv -> HaloM a -> (a,[String])
runHaloM env (HaloM m) = evalRWS m env Nothing

capturePtrs :: HaloM a -> HaloM (a,[Var])
capturePtrs m = do
    let nested_err = error "capturePtrs: Internal error, running nested capturePtrs"
    check <- get
    when (isNothing check) nested_err
    put (Just emptyVarSet)
    res <- m
    m_vs <- get
    put Nothing
    case m_vs of
        Just vs -> return (res,varSetElems vs)
        Nothing -> nested_err

usePtr :: Var -> HaloM ()
usePtr v = do
    write $ "Registering " ++ show v ++ " as a used pointer"
    modify k
  where
    k Nothing   = error "usePtr: Internal error, ptr used without capturePtrs"
    k (Just vs) = Just (extendVarSet vs v)

-- | The translation monad
--
--   Reader : see HaloEnv above
--   Writer : Debug strings
--   State  : Set of used function pointers
newtype HaloM a = HaloM (RWS HaloEnv [String] (Maybe VarSet) a)
  deriving (Applicative,Monad,Functor
           ,MonadReader HaloEnv
           ,MonadWriter [String]
           ,MonadState (Maybe VarSet)
           )

substContext :: Subst -> HaloEnv -> HaloEnv
substContext s env = env
    { args = map (substExpr (text "substContext:args") s) (args env)
    , constr = map (substConstr s) (constr env)
    }

-- | Write a debug message
write :: MonadWriter [String] m => String -> m ()
write = tell . return
