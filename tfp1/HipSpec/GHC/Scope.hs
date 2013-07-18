module HipSpec.GHC.Scope (getNamedThings) where

import GHC hiding (Sig)

import Data.Map (Map)
import qualified Data.Map as M

-- | Getting the names in scope
--
--   Context for evaluation needs to be set before
getNamedThings :: (Id -> Id) -> Ghc (Map Name TyThing)
getNamedThings fix_id = do

    -- Looks up a name and tries to associate it with a typed thing
    let lookup_name :: Name -> Ghc (Maybe (Name,TyThing))
        lookup_name n = fmap (fmap (\ (tyth,_,_) -> (n,tyth))) (getInfo n)

    -- Get the types of all names in scope
    ns <- getNamesInScope
    maybe_named_things <- mapM lookup_name ns

    return $ M.fromList
        [ (n,mapTyThingId fix_id tyth)
        | Just (n,tyth) <- maybe_named_things
        ]

mapTyThingId :: (Id -> Id) -> TyThing -> TyThing
mapTyThingId k (AnId i) = AnId (k i)
mapTyThingId _ tyth     = tyth

