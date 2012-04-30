module Risers where

risersBy :: (a -> a -> Bool) -> [a] -> [[a]]
risersBy le [] = []
risersBy le [x] = [[x]]
risersBy le (x:y:etc) = if le x y
                           then (x:s):ss
                           else [x]:(s:ss)
    where (s:ss) = risersBy le (y:etc)