{-# LANGUAGE ViewPatterns, PatternGuards #-}
module HipSpec.Trans.Unify (runMatch, runMatches) where

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe

import Control.Monad
import Control.Monad.Logic

import Type

import Halo.Shared

-- import Debug.Trace
trace = flip const

data Constraint = TyVar :=: Type

instance Show Constraint where
  show (a :=: t) = showOutputable a ++ " = " ++ showOutputable t

runMatch :: Ord q => [(q,Type)] -> [(Type,s)] -> Maybe (Map q s)
runMatch qs types = listToMaybe (observeMany 1 (match qs types))

runMatches :: Ord q => [(q,Type)] -> [(Type,s)] -> [Map q s]
runMatches qs types = observeAll (match qs types)

match :: Ord q => [(q,Type)] -> [(Type,s)] -> Logic (Map q s)
match = go []
  where
    go cs []         _     = return M.empty
    go cs ((q,t):qs) types = do

        ((_t,s),types',cs') <- extractBy (\ (t',_) -> t `instanceOf` t') types

        let cs_new = cs ++ cs'

        guard (not (conflict cs_new))

        rest <- go cs_new qs types'

        return $ M.insert q s rest

conflict cs =
    let res = conflict' cs
    in  trace ("conflict " ++ show cs ++ " = " ++ show res) res

conflict' :: [Constraint] -> Bool
conflict' []     = False
conflict' (c:cs) = any (c `conflicting`) cs || conflict' cs

(a :=: t1) `conflicting` (b :=: t2) = a == b && not (t1 `eqType` t2)


extractBy :: (a -> Maybe [Constraint]) -> [a] -> Logic (a,[a],[Constraint])
extractBy k (x:xs) =
    (case k x of
        Just cs -> (return (x,xs,cs))
        Nothing -> mzero
    ) `mplus` do
        (y,ys,cs) <- extractBy k xs
        return (y,x:ys,cs)
extractBy _ [] = mzero

instanceOf :: Type -> Type -> Maybe [Constraint]
t1 `instanceOf` t2 = res
{-
    trace (showOutputable t1 ++ " `instanceOf` " ++
           showOutputable t2 ++ " = " ++ show res) res
           -}
  where res = t1 `instanceOf'` t2

instanceOf' :: Type -> Type -> Maybe [Constraint]
instanceOf' (repType' -> r) (repType' -> s)
    | Just a <- getTyVar_maybe r
    = case getTyVar_maybe s of
        Just b | a == b -> return []
        _               -> return [a :=: s]

    | Just (a,u) <- splitAppTy_maybe r
    , Just (b,v) <- splitAppTy_maybe s
    = liftM2 (++) (a `instanceOf` b) (u `instanceOf` v)

    | Just (a,u) <- splitFunTy_maybe r
    , Just (b,v) <- splitFunTy_maybe s
    = liftM2 (++) (a `instanceOf` b) (u `instanceOf` v)

    | Just (c1,as) <- splitTyConApp_maybe r
    , Just (c2,bs) <- splitTyConApp_maybe s
    = do
        guard (c1 == c2)
        liftM concat (zipWithM instanceOf as bs)

    | otherwise = mzero

{-
occurs :: TyVar -> Type -> Bool
occurs a r
    | Just b <- getTyVar_maybe r
    = a == b

    | Just (u,v) <- splitAppTy_maybe r
    = (a `occurs` u) || (a `occurs` v)

    | Just (u,v) <- splitFunTy_maybe r
    = (a `occurs` u) || (a `occurs` v)

    | Just (c1,ts) <- splitTyConApp_maybe r
    = any (occurs a) ts

    | otherwise = mzero
    -}
