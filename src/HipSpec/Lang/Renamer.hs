{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module HipSpec.Lang.Renamer where

import Control.Monad.State
import Control.Monad.Reader

import Data.Traversable (Traversable)
import qualified Data.Traversable as T

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Control.Arrow

import Data.Bitraversable (Bitraversable)
import qualified Data.Bitraversable as B

type RenameM a b = ReaderT (Suggestor a b) (State (Map a b,Set b))

type Suggestor a b = a -> [b]

disambig :: (a -> String) -> Suggestor a String
disambig f (f -> x) = x : [ x ++ show (i :: Int) | i <- [2..] ]

runRenameM :: Ord b => Suggestor a b -> [b] -> RenameM a b r -> r
runRenameM f block m = evalState (runReaderT m f) (M.empty,S.fromList block)

insert :: (Ord a,Ord b) => a -> RenameM a b b
insert n = go =<< asks ($ n)
  where
    go (s:ss) = do
        u <- gets snd
        if s `S.member` u then go ss else do
            modify (M.insert n s *** S.insert s)
            return s
    go [] = error "ran out of names!?"

insertMany :: (Ord a,Ord b) => [a] -> RenameM a b [b]
insertMany = mapM insert

lkup :: (Ord a,Ord b) => a -> RenameM a b b
lkup n = do
    m_s <- gets (M.lookup n . fst)
    case m_s of
        Just s  -> return s
        Nothing -> insert n

rename :: (Ord a,Ord b,Traversable t) => t a -> RenameM a b (t b)
rename = T.mapM lkup

renameWith :: (Ord a,Ord b,Traversable t) => Suggestor a b -> t a -> t b
renameWith f = runRenameM f [] . rename

renameBi :: (Ord a,Ord b,Bitraversable t) => t a a -> RenameM a b (t b b)
renameBi = B.bimapM lkup lkup

renameBiWith :: (Ord a,Ord b,Bitraversable t) => Suggestor a b -> t a a -> t b b
renameBiWith f = runRenameM f [] . renameBi

renameBi2 :: (Ord a,Ord b,Ord c,Bitraversable t) => t a b -> RenameM (Either a b) c (t c c)
renameBi2 = B.bimapM (lkup . Left) (lkup . Right)

renameBi2With :: (Ord a,Ord b,Bitraversable t) => Suggestor a b -> t a a -> t b b
renameBi2With f = runRenameM f [] . renameBi

disambig2 :: (a -> String) -> (b -> String) -> Suggestor (Either a b) String
disambig2 f _ (Left a)  = disambig f a
disambig2 _ g (Right b) = disambig g b

