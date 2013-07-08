module Inner where

map :: (a -> b) -> [a] -> [b]
map f = go
  where
    go (x:xs) = f x : go xs
    go []     = []
