module App where

k f x = case f x of
          (g,h) -> (g x,case h x of (k,_) -> k x (g x))

