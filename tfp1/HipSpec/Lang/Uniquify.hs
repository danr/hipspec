-- | One could think that every identifier in GHC Core is supposed to be Unique,
-- but this is not the case. This module cleans up this mess.
--
-- The targets are local lets that happily gets the same name, and also
-- scrutinee vars that can get the same name if they are never used.
module HipSpec.Lang.Uniquify where

import CoreSyn

import UniqSupply

import Var

import Control.Monad.Reader
import Control.Applicative

import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe (fromMaybe)

type UQ m a = ReaderT (Map Var Var) m a

runUQ :: (Applicative m,MonadUnique m) => UQ m a -> m a
runUQ m = runReaderT m M.empty

insertVar :: (Applicative m,MonadUnique m) => Var -> UQ m a -> UQ m a
insertVar x m = do
    my <- asks (M.lookup x)
    x' <- case my of
        Just{} -> do
            u <- lift getUniqueM
            return (setVarUnique x u)
        Nothing -> return x
    local (M.insert x x') m

insertVars :: (Applicative m,MonadUnique m) => [Var] -> UQ m a -> UQ m a
insertVars xs m = foldr insertVar m xs

lookupVar :: (Applicative m,MonadUnique m) => Var -> UQ m Var
lookupVar x = fromMaybe x <$> asks (M.lookup x)

uqBind :: (Applicative m,MonadUnique m) => CoreBind -> (CoreBind -> UQ m a) -> UQ m a
uqBind (NonRec v e) k = insertVar v (k =<< NonRec <$> lookupVar v <*> uqExpr e)
uqBind (Rec vses)   k = insertVars (map fst vses) $ k . Rec =<< sequence
    [ (,) <$> lookupVar v <*> uqExpr e | (v,e) <- vses ]

uqExpr :: (Applicative m,MonadUnique m) => CoreExpr -> UQ m CoreExpr
uqExpr e0 = case e0 of
    Var x           -> Var <$> lookupVar x
    App e1 e2       -> App <$> uqExpr e1 <*> uqExpr e2
    Let bs e        -> uqBind bs $ \ bs' -> Let bs' <$> uqExpr e
    Lam x e         -> insertVar x (Lam <$> lookupVar x <*> uqExpr e)
    Case s x t alts -> do
        s' <- uqExpr s
        insertVar x $ do
            x' <- lookupVar x
            Case s' x' t <$> mapM uqAlt alts
    Cast e c        -> (`Cast` c) <$> uqExpr e
    Tick tk e       -> Tick tk <$> uqExpr e
    Type{}          -> return e0
    Lit{}           -> return e0
    Coercion{}      -> return e0

uqAlt :: (Applicative m,MonadUnique m) => CoreAlt -> UQ m CoreAlt
uqAlt (pat,bs,e) = insertVars bs ((,,) pat <$> mapM lookupVar bs <*> uqExpr e)

