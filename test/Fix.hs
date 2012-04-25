module Fix where

fix_let f = let x = f x in x

fix_where f = x
  where x = f x

fix f = f (fix f)
