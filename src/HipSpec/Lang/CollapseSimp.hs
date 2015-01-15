{-# LANGUAGE ScopedTypeVariables,ViewPatterns #-}
module HipSpec.Lang.CollapseSimp (collapseSimp) where

import Data.Traversable
import Data.Generics.Geniplate
import HipSpec.Lang.Simple
import HipSpec.Utils
import Control.Monad.State
import Data.Either

renameVars :: Traversable f => (a -> Bool) -> f a -> f (Either a Int)
renameVars is_var t = traverse rename t `evalState` 0
  where
    rename x | is_var x = do
        s <- get
        put (s+1)
        return (Right s)
    rename x = return (Left x)

isLocal :: Eq a => Function a -> a -> Bool
isLocal fn y = or $
    [ y == fn_name fn ] ++
    [ y == x | x <- fn_args fn ] ++
    [ y == x | Lcl x _ <- universeBi fn ] ++
    [ y == x | TyVar x <- universeBi fn ] ++
    [ y == x | Forall tvs _ <- universeBi fn, x <- tvs ]

renameFn :: Eq a => Function a -> Function (Either a Int)
renameFn fn = renameVars (isLocal fn) fn

-- If we have
--   f x = E[x]
--   g y = E[y]
-- then we remove g (!) and replace it with f everywhere
collapseSimp :: forall a . Eq a => [Function a] -> [Function a]
collapseSimp fs0 = map (fmap rename) survivors
  where
    rfs :: [(Function a,Function (Either a Int))]
    rfs = [ (f,renameFn f) | f <- fs0 ]

    renamings :: [(a,a)]
    survivors :: [Function a]
    (renamings,survivors) = partitionEithers
        [ case [ (fn_name f,fn_name g) | (g,rg) <- prev , rf == rg ] of
            []   -> Right f -- f is better
            fg:_ -> Left fg -- g is better
        | ((f,rf),prev) <- withPrevious rfs
        ]

    rename :: a -> a
    rename x = case lookup x renamings of
        Just y  -> y
        Nothing -> x

{-
   NB: This cannot really be done since QuickSpec might still want to talk
   about these removed functions.
   We should return the rename map and run it over all functions that come from QuickSpec

-- If we have
--    g x y = f x y
-- then we remove g and replace it with f everywhere
removeDuplicates :: forall a . Eq a => [Function a] -> [Function a]
removeDuplicates fs0 = map (fmap rename) $ filter ((`notElem` remove) . fn_name) fs0
  where
    remove = map fst renamings

    renamings =
      [ (g,f)
      | Function g _ xs (Just (Body (collectArgs -> (Gbl f _ _,ys)))) <- fs0
      , length xs == length ys
      , xs == [ y | Lcl y _ <- ys ]
      ]

    rename :: a -> a
    rename x = case lookup x renamings of
        Just y  -> y
        Nothing -> x

-}
