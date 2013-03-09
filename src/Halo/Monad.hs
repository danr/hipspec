{-# LANGUAGE
        FlexibleContexts,
        GeneralizedNewtypeDeriving,
        NamedFieldPuns,
        RecordWildCards
  #-}
{-

    The Halo Monad. Keeps track of:

        * Skolemised variables

            Add skolemised variables with `addSkolem' and `addSkolems'.

        * Configuration

            A copy of the HaloConf.

        * Debug messages

        * Errors

            Some things are unsupported for now, like literals.
            Trying to translate these throws an error.
            In Halo.Binds, these make the program crash if you
            ever try to translate that particular subtheory.

            Now also sometimes when monoType fails

    Things only needed in Halo.Binds:

        * The current function

            With some restructuring this could be removed.

        * The arguments to the current function

            Arguments are CoreExpr because they get substituted when
            casing upon.

        * Constraints

            Are also subject to substitution from case expressions.

-}
module Halo.Monad where

import CoreSubst
import CoreSyn
import DataCon
import Id
import Outputable
import TyCon
import Unique
import VarSet

import Halo.Conf
import Halo.Constraints
import Halo.Shared
import Halo.Util
import Halo.Subtheory
import Halo.FOL.Abstract
import Halo.MonoType

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)

import Data.Maybe

import Control.Monad.RWS
import Control.Monad.Error


-- | The Environment
data HaloEnv = HaloEnv
    { current_fun :: Var
    -- ^ Current function
    , args        :: [CoreExpr]
    -- ^ Arguments to current function
    --   CoreExprs instead of Vars because they can get substituted
    , qvars       :: Set Var
    -- ^ Quantified variables
    , skolems     :: Map Var Term'
    -- ^ Skolemised variables
    , constr      :: [Constraint]
    -- ^ Constraints
    , conf        :: HaloConf
    -- ^ Configuration
    }


addQuantVars :: [Var] -> HaloEnv -> HaloEnv
addQuantVars vs env = env { qvars = S.toList vs `S.union` qvars env }

-- | Registers a variable as a skolem variable
addSkolem :: Var -> MonoType' -> HaloEnv -> HaloEnv
addSkolem v t env = env { skolems = M.insert v (skolem v t) (skolems env) }

-- | Registers many skolem variables
addSkolems :: [(Var,MonoType')] -> HaloEnv -> HaloEnv
addSkolems vsts env = env
    { skolems = M.fromList [ (v,skolem v t) | (v,t) <- vsts ] `M.union` skolems env
    }

-- | Pushes a new constraint to an environment
pushConstraint :: Constraint -> HaloEnv -> HaloEnv
pushConstraint c = pushConstraints [c]

-- | Pushes many new constraints to an environment
pushConstraints :: [Constraint] -> HaloEnv -> HaloEnv
pushConstraints cs env = env { constr = cs ++ constr env }

-- | Make the environment
mkEnv :: HaloConf -> [TyCon] -> [CoreBind] -> HaloEnv
mkEnv conf@HaloConf{..} ty_cons program =
    let -- Remove the unnecessary SCC information
        binds :: [(Var,CoreExpr)]
        binds = flattenBinds program


    in  HaloEnv
            { current_fun = error "initEnv: current_fun"
            , args        = []
            , skolems     = M.empty
            , constr      = noConstraints
            , conf        = conf
            }

-- | The translation monad
--
--   Reader : see HaloEnv above
--   Writer : Debug strings
newtype HaloM a = HaloM (ErrorT String (ReaderT HaloEnv (Writer [String] a)))
  deriving
      (Functor,Applicative,Monad
      ,MonadReader HaloEnv
      ,MonadWriter [String]
      ,MonadError String
      )

runHaloM :: HaloEnv -> HaloM a -> (a,[String])
runHaloM env hm = case runHaloMsafe env hm of
    (err_or_res,msg) -> (either error id err_or_res,msg)

runHaloMsafe :: HaloEnv -> HaloM a -> (Either String a,[String])
runHaloMsafe env (HaloM m) = runWriter (runReaderT (runErrorT m) env)

-- | Substitute the entire context, i.e. arguments and constraints
substContext :: Subst -> HaloEnv -> HaloEnv
substContext s env = env
    { args    = map (substExpr (text "substContext:args") s) (args env)
    , constr  = map (substConstr s) (constr env)
    }

-- | Write a debug message
write :: MonadWriter [String] m => String -> m ()
write = tell . return

