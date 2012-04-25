module Lists where

import Prelude (Bool(..))

otherwise = True

insert (<) x [] = [x]
insert (<) x (y:ys) | x < y     = x:y:ys
                    | otherwise = y:insert (<) x ys

isort (<) [] = []
isort (<) (x:xs) = insert (<) x (isort (<) xs)

swap [x,y] = [y,x]
rot [x,y,z] = [z,x,y]