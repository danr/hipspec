{-# LANGUAGE FlexibleContexts #-}
-- | Some common utilites for a MonadReader that keeps track of typed variables in scope
module HipSpec.Lang.TypedScope where

import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as M

type Scope = Map

-- | Make a scope
makeScope :: Ord v => [(v,t)] -> Scope v t
makeScope = M.fromList

-- | Extend the scope with a list of variables
extendScope :: (MonadReader (Scope v t) m,Ord v) => [(v,t)] -> m a -> m a
extendScope = local . M.union . makeScope

-- | Removes an entry from the scope
removeFromScope :: (MonadReader (Scope v t) m,Ord v) => v -> m a -> m a
removeFromScope = local . M.delete

-- | Clear the scope
clearScope :: MonadReader (Scope v t) m => m a -> m a
clearScope = local (const emptyScope)

-- | The empty scope
emptyScope :: Scope v t
emptyScope = M.empty

-- | True if the variable is in scope
inScope :: (MonadReader (Scope v t) m,Ord v) => v -> m Bool
inScope = asks . M.member

-- | Type of the variable if it is in scope
typeOf :: (MonadReader (Scope v t) m,Ord v) => v -> m (Maybe t)
typeOf = asks . M.lookup

-- | Gets the current scope
getScope :: (MonadReader (Scope v t) m,Ord v) => m [(v,t)]
getScope = asks M.toList
