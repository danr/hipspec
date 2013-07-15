{-# LANGUAGE FlexibleContexts,MultiParamTypeClasses,FlexibleInstances,
             TypeSynonymInstances,ScopedTypeVariables,FunctionalDependencies #-}
-- | Some common utilites for a MonadReader that keeps track of variables in scope
module Scope where

import Control.Monad.Reader

import Data.Set (Set)
import qualified Data.Set as S

type Scope = Set

class HasScope v t | t -> v where
    get_scope :: t -> Scope v
    mod_scope :: (Scope v -> Scope v) -> t -> t

instance HasScope v (Scope v) where
    get_scope = id
    mod_scope = id

-- | Make a scope
makeScope :: Ord v => [v] -> Set v
makeScope = S.fromList

-- | Extend the scope with a list of variables
extendScope :: (HasScope v t,MonadReader t m,Ord v) => [v] -> m a -> m a
extendScope = local . mod_scope . S.union . makeScope

-- | Removes an entry from the scope
removeFromScope :: (HasScope v t,MonadReader t m,Ord v) => v -> m a -> m a
removeFromScope = local . mod_scope . S.delete

-- | Clear the scope
clearScope :: forall v t m a . (HasScope v t,MonadReader t m) => m a -> m a
clearScope = local (mod_scope (const (emptyScope :: Scope v)))

-- | The empty scope
emptyScope :: Scope v
emptyScope = S.empty

-- | True if the variable is in scope
inScope :: (HasScope v t,MonadReader t m,Ord v) => v -> m Bool
inScope x = asks (S.member x . get_scope)

-- | Returns only the elments that are in scope
pluckScoped :: (HasScope v t,MonadReader t m,Ord v) => [v] -> m [v]
pluckScoped = filterM inScope

-- | Gets the current scope
getScope :: (HasScope v t,MonadReader t m,Ord v) => m [v]
getScope = asks (S.toList . get_scope)

