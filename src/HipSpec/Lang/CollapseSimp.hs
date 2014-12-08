module HipSpec.Lang.CollapseSimp (collapseSimp) where

import HipSpec.Lang.Simple
import Control.Monad
import Control.Monad.State

renameVars :: Traversable f => (a -> Bool) -> f a -> f (Either a Int)
renameVars is_var = flip evalState 0 $ traverse $ \ x ->
    if is_var x then
        s <- get
        put (s+1)
        return (Right s)
    else return (Left x)

isLocal :: Eq a => Function a -> a -> Bool
isLocal fn y = or $
    [ y == fn_name fn ] ++
    [ y == x | Lcl x _ <- universeBi fn ] ++
    [ y == x | TyVar x <- universeBi fn ] ++
    [ y == x | ForAll tvs _ <- universeBi fn, x <- tvs ]

renameFn :: Eq a => Function a -> Function (Either a Int)
renameFn fn = renameVars (isLocal fn) fn

-- If we have
--   f x = E[x]
--   g y = E[y]
-- then we remove g (!) and replace it with f everywhere
collapseSimp :: Eq a => [Function a] -> [Function a]
collapseSimp fs0 = map (fmap rename) fs0
  where
    rfs = [ (f,renameFn f) | f <- fs0 ]

    renamings =
        [ (f,g)
        | ((f,rf),prev) <- withPrevious rfs
        , (g,rg) <- prev
        , rf == rg
        ]

    rename x = case lookup x renamings of
        Just y  -> y
        Nothing -> x

