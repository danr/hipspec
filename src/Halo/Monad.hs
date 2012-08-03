{-# LANGUAGE
        FlexibleContexts,
        GeneralizedNewtypeDeriving,
        NamedFieldPuns,
        RecordWildCards
  #-}
{-

    The Halo Monad. Keeps track of:

        * Arities of top level functions

            This is needed to determine if app:s and pointers need to
            be introduced when translating expressions.

        * Skolemised variables

            Add skolemised variables with `addSkolem' and `addSkolems'.

        * Configuration

            A copy of the HaloConf.

        * Function pointers used

            Capture this with capturePtrs. If you catch an error
            inside this, use cleanUpFailedCapture.

            (With reordering the monad stack maybe the cleanup could
            get removed.)

        * Debug messages

        * Errors

            Some things are unsupported for now, like literals.
            Trying to translate these throws an error.
            In Halo.Binds, these make the program crash if you
            ever try to translate that particular subtheory.

    Things only needed in Halo.Binds:

        * The current function

            With some restructuring this could be removed.

        * The arguments to the current function

            Arguments are CoreExpr because they get substituted when
            casing upon.

        * Constraints

            Are also subject to substitution from case expressions.

        * Min-set

            Expressions cased on.

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
import Halo.PrimCon
import Halo.Shared
import Halo.Util

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe

import Control.Monad.RWS
import Control.Monad.Error

-- | Map associating each function/CAF with its arity
type ArityMap = Map Var Int

-- | Debug the arity map
showArityMap :: ArityMap -> [String]
showArityMap m =
    [ show k ++ "(" ++ show (getUnique k) ++ "):" ++ show v
    | (k,v) <- M.toList m ]

-- | The Environment
data HaloEnv = HaloEnv
    { arities     :: ArityMap
    -- ^ Arities of top level definitions
    , current_fun :: Var
    -- ^ Current function
    , args        :: [CoreExpr]
    -- ^ Arguments to current function
    , skolems     :: [Var]
    -- ^ Skolemised variables
    , constr      :: [Constraint]
    -- ^ Constraints
    , min_set     :: [CoreExpr]
    -- ^ Current min-set (of cased scrutinees) when translating a bind
    , conf        :: HaloConf
    -- ^ Configuration
    }

-- | Registers a variable as a skolem variable
addSkolem :: Var -> HaloEnv -> HaloEnv
addSkolem v env = env { skolems = v:skolems env }

-- | Registers many skolem variables
addSkolems :: [Var] -> HaloEnv -> HaloEnv
addSkolems vs env = env { skolems = vs ++ skolems env }

-- | Pushes a new constraint to an environment
pushConstraint :: Constraint -> HaloEnv -> HaloEnv
pushConstraint c = pushConstraints [c]

-- | Pushes many new constraints to an environment
pushConstraints :: [Constraint] -> HaloEnv -> HaloEnv
pushConstraints cs env = env { constr = cs ++ constr env }

-- | Extends the arities
extendArities :: ArityMap -> HaloEnv -> HaloEnv
extendArities am env = env { arities = am `M.union` arities env }

-- | Lookup the arity for a function
lookupArity :: Var -> HaloM (Maybe Int)
lookupArity v = do
    m <- asks arities
    return $ M.lookup v m

-- | Extend the min expressions set
extendMinSet :: CoreExpr -> HaloEnv -> HaloEnv
extendMinSet e env = env { min_set = e : min_set env }

-- | Make the environment
mkEnv :: HaloConf -> [TyCon] -> [CoreBind] -> HaloEnv
mkEnv conf@HaloConf{..} ty_cons program =
    let -- Remove the unnecessary SCC information
        binds :: [(Var,CoreExpr)]
        binds = flattenBinds program

        data_arities :: [(Var,Int)]
        data_arities =
            [ (primId c,0) | c <- [UNR,BAD], unr_and_bad ] ++
            [ (dc_id,arity)
            | ty_con <- ty_cons
            , let dcs = tyConDataCons ty_con
            , dc <- dcs
            , let dc_id           = dataConWorkId dc
                  (_,_,ty_args,_) = dataConSig dc
                  arity           = length ty_args
            ]

        -- Arity of each function (Arities from other modules are also needed)
        arities :: ArityMap
        arities = M.fromList $ [ (v,exprArity e) | (v,e) <- binds ]
                               ++ data_arities

    in  HaloEnv
            { arities     = arities
            , current_fun = error "initEnv: current_fun"
            , args        = []
            , skolems     = []
            , constr      = noConstraints
            , min_set     = []
            , conf        = conf
            }

-- | The translation monad
--
--   Reader : see HaloEnv above
--   Writer : Debug strings
--   State  : Set of used function pointers
newtype HaloM a = HaloM (ErrorT String (RWS HaloEnv [String] (Maybe VarSet)) a)
  deriving
      (Functor,Applicative,Monad
      ,MonadReader HaloEnv
      ,MonadWriter [String]
      ,MonadState (Maybe VarSet)
      ,MonadError String
      )

runHaloM :: HaloEnv -> HaloM a -> (a,[String])
runHaloM env hm = case runHaloMsafe env hm of
    (err_or_res,msg) -> (either error id err_or_res,msg)

runHaloMsafe :: HaloEnv -> HaloM a -> (Either String a,[String])
runHaloMsafe env (HaloM m) = evalRWS (runErrorT m) env Nothing

capturePtrs :: HaloM a -> HaloM (a,[Var])
capturePtrs m = do
    let nested_err = throwError "capturePtrs: Internal error, nested captures"
    check <- get
    when (isJust check) nested_err
    put (Just emptyVarSet)
    res <- m
    m_vs <- get
    put Nothing
    case m_vs of
        Just vs -> return (res,varSetElems vs)
        Nothing -> nested_err

-- | Register a pointer as used. Must be run inside capturePtrs
usePtr :: Var -> HaloM ()
usePtr v = do
    write $ "Registering " ++ show v ++ " as a used pointer"
    m_vs <- get
    case m_vs of
        Nothing -> throwError "usePtr: Internal error, ptr used without capture"
        Just vs -> put $ Just (extendVarSet vs v)

-- | If the translation of an expression fails, we need to clean up
--   the capturing of function pointers
cleanUpFailedCapture :: HaloM ()
cleanUpFailedCapture = put Nothing

-- | Substitute the entire context, i.e. arguments and constraints, and min_set
substContext :: Subst -> HaloEnv -> HaloEnv
substContext s env = env
    { args    = map (substExpr (text "substContext:args") s) (args env)
    , constr  = map (substConstr s) (constr env)
    , min_set = map (substExpr (text "substContext:min_set") s) (min_set env)
    }

-- | Write a debug message
write :: MonadWriter [String] m => String -> m ()
write = tell . return
