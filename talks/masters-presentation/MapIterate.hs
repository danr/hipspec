module MapIterate where

map :: (a -> b) -> [a] -> [b]
map f []       = []
map f (x : xs) = f x : map f xs

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

prop_map_iterate :: (a -> a) -> a -> Prop [a]
prop_map_iterate f x = map f (iterate f x) =:= iterate f (f x)

