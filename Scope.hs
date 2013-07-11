{-# LANGUAGE FlexibleContexts #-}
-- | Some common utilites for a MonadReader that keeps track of variables in scope
module Scope where

import Control.Monad.Reader

import Data.Set (Set)
import qualified Data.Set as S

type Scope = Set

-- | Make a scope
makeScope :: Ord v => [v] -> Set v
makeScope = S.fromList

-- | Extend the scope with a list of variables
extendScope :: (MonadReader (Set v) m,Ord v) => [v] -> m a -> m a
extendScope = local . S.union . makeScope

-- | Removes an entry from the scope
removeScope :: (MonadReader (Set v) m,Ord v) => v -> m a -> m a
removeScope = local . S.delete

-- | Clear the scope
clearScope :: MonadReader (Set v) m => m a -> m a
clearScope = local (const emptyScope)

-- | The empty scope
emptyScope :: Set v
emptyScope = S.empty

-- | True if the variable is in scope
inScope :: (MonadReader (Set v) m,Ord v) => v -> m Bool
inScope = asks . S.member

-- | Returns only the elments that are in scope
pluckScoped :: (MonadReader (Set v) m,Ord v) => [v] -> m [v]
pluckScoped = filterM inScope

-- | Gets the current scope
getScope :: (MonadReader (Set v) m,Ord v) => m [v]
getScope = asks S.toList
