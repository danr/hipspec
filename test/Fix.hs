module Fix where

fix_let f = let x = f x in x

fix_where f = x
  where x = f x

fix f = f (fix f)

-- with g = id, equivalent to fix
fix_wat :: (a -> b) -> (b -> a) -> b
fix_wat f g = x
  where x = f (g x)

fixstr :: ((a -> b) -> a -> b) -> a -> b
fixstr f = go
  where
    {-# NOINLINE go #-}
    go a = f (fixstr f) a

