module HipSpec.Utils.PopMap (PopMap,insert,pop,empty,fromList,reverseMap) where

import Data.Map (Map)
import qualified Data.Map as M

-- | A multi-map which supports popping elements
newtype PopMap k v = PopMap { toMap :: Map k [v] }
  deriving (Eq,Ord,Show)

-- | Not exported
withUnderlying :: (Map k [v] -> Map k [v]) -> PopMap k v -> PopMap k v
withUnderlying f (PopMap m) = PopMap (f m)

-- | An empty pop map
empty :: PopMap k v
empty = PopMap M.empty

-- | Insert a pair into the map
insert :: Ord k => k -> v -> PopMap k v -> PopMap k v
insert k v = withUnderlying $ M.alter f k
  where
    f Nothing   = Just [v]
    f (Just vs) = Just (v:vs)

-- | Try to pop an element associated with a key
pop :: Ord k => k -> PopMap k v -> Maybe (v,PopMap k v)
pop k (PopMap m) = case M.lookup k m of
    Just (v:_) -> Just (v,PopMap (M.update f k m))
    _          -> Nothing
  where
    f (_:vs) = Just vs
    f _      = Nothing

fromList :: Ord k => [(k,v)] -> PopMap k v
fromList = foldr (uncurry insert) empty

-- | Given a map where a value can get pointed to from several keys,
--   reverse it and put it into a PopMap.
reverseMap :: Ord v => Map k v -> PopMap v k
reverseMap = fromList . map swap . M.toList
  where
    swap (x,y) = (y,x)
