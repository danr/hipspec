module HipSpec.Sig.Scope where

import GHC hiding (Sig)

import qualified Data.Map as M
import Data.Map (Map)

import TysWiredIn
import DataCon (dataConName)
import TyCon (TyCon,tyConName)
import BasicTypes (TupleSort(BoxedTuple))

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

    return $ M.fromList $
        [ (n,mapTyThingId fix_id tyth)
        | Just (n,tyth) <- maybe_named_things
        ] ++
        -- These built in constructors are not in scope by default (!?), so we add them here
        -- Note that tuples up to size 8 are only supported...
        concat
            [ (tyConName tc,ATyCon tc) :
              [ (dataConName dc,ADataCon dc) | dc <- tyConDataCons tc ]
            | tc <- [listTyCon,unitTyCon,pairTyCon] ++ map (tupleTyCon BoxedTuple) [3..8]
            ]

mapTyThingId :: (Id -> Id) -> TyThing -> TyThing
mapTyThingId k (AnId i) = AnId (k i)
mapTyThingId _ tyth     = tyth

inScope :: String -> Ghc Bool
inScope s = handleSourceError (\ _ -> return False) $ do
    xs <- parseName s
    return $ if null xs then False else True

