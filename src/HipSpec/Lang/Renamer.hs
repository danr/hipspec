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

type RenameM a = ReaderT (Suggestor a) (State (Map a String,Set String))

type Suggestor a = a -> String

runRenameM :: Suggestor a -> [String] -> RenameM a b -> b
runRenameM f block m = evalState (runReaderT m f) (M.empty,S.fromList block)

insert :: Ord a => a -> RenameM a String
insert n = do
    s <- asks ($ n)
    let ss = s : [ s ++ show i | i <- [(2 :: Int)..] ]
    go ss
  where
    go (s:ss) = do
        u <- gets snd
        if s `S.member` u then go ss else do
            modify (M.insert n s *** S.insert s)
            return s
    go [] = error "ran out of names!?"

insertMany :: Ord a => [a] -> RenameM a [String]
insertMany = mapM insert

lkup :: Ord a => a -> RenameM a String
lkup n = do
    m_s <- gets (M.lookup n . fst)
    case m_s of
        Just s  -> return s
        Nothing -> insert n

rename :: (Ord a,Traversable t) => t a -> RenameM a (t String)
rename = T.mapM lkup

renameWith :: (Ord a,Traversable t) => Suggestor a -> t a -> t String
renameWith f = runRenameM f [] . rename

