module Let where

data ABC = A | B | C

isA :: ABC -> Bool
isA A = True
isA _ = False

toABC :: Bool -> ABC
toABC True  = A
toABC False = C

cycling :: [Bool] -> [ABC] -> ([ABC],[Bool])
cycling bs abcs = (map toABC bs,map isA abcs)
  where
    map :: (a -> b) -> [a] -> [b]
    map f (x:xs) = f x : map f xs
    map f []     = []

