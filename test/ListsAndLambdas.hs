module ListsAndLambdas where

import Prelude ()

f . g = \x -> f (g x)

flip f = \x y -> f y x


foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     =  z
foldr f z (x:xs) =  f x (foldr f z xs)


unzip            :: [(a,b)] -> ([a],[b])
unzip            =  foldr (\(a,b) (as,bs) -> (a:as,b:bs)) ([],[])


unzip3           :: [(a,b,c)] -> ([a],[b],[c])
unzip3           =  foldr (\(a,b,c) (as,bs,cs) -> (a:as,b:bs,c:cs))
                          ([],[],[])


map' :: (a -> b) -> [a] -> [b]
map' f xs = foldr (\x acc -> f x : acc) [] xs

