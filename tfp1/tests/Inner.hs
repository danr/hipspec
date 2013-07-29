module Inner where

map :: (a -> b) -> [a] -> [b]
map f = go
  where
    go (x:xs) = f x : go xs
    go []     = []


-- | This one does not get inlined
--   Eta reduction? Handle this special case?
map' :: (a -> b) -> [a] -> [b]
map' f xs = go xs
  where
    go (x:xs) = f x : go xs
    go []     = []
