module Halo.Unfoldings (fixUnfoldings) where

import Data.Map (Map)
import qualified Data.Map as M

import Control.Applicative
import Data.Traversable (sequenceA)

import Control.Monad.Reader

import CoreSyn
import CoreUnfold
import Id

-- | Ties the knot!
fixUnfoldings :: [CoreBind] -> [CoreBind]
fixUnfoldings bs = map (idMap lkup) bs'
  where
    bs' :: [CoreBind]
    bs' = (mapM (exprMap k) bs) lkup

    bind_map :: Map Id CoreExpr
    bind_map = M.fromList (flattenBinds bs')

    lkup :: Id -> Id
    lkup x = case M.lookup x bind_map of
        Just lhs -> x `setIdUnfoldingLazily` mkCompulsoryUnfolding lhs
        Nothing -> x

    h :: Id -> (Id -> Id) -> Id
    h x = do
        m <- ask
        return (m x)

    k :: CoreExpr -> (Id -> Id) -> CoreExpr
    k = boringCases h k

-- | Maps an expression fun over binds
exprMap :: Applicative f => (CoreExpr -> f CoreExpr) -> CoreBind -> f CoreBind
exprMap f (NonRec v e) = NonRec v <$> f e
exprMap f (Rec vses)   = Rec <$> sequenceA [ (,) v <$> f e | (v,e) <- vses ]

-- | Maps an identifier fun over binds
idMap :: (Id -> Id) -> CoreBind -> CoreBind
idMap f (NonRec v e) = NonRec (f v) e
idMap f (Rec vses)   = Rec [ (f v,e) | (v,e) <- vses ]

-- | Fills in all boring cases for you
boringCases :: Applicative f => (Var -> f Var) -> (CoreExpr -> f CoreExpr) -> CoreExpr -> f CoreExpr
boringCases h f t = case t of
    Var x -> Var <$> h x
    Lit{} -> pure t
    App e1 e2 -> App <$> f e1 <*> f e2
    Lam x e -> Lam x <$> f e
    Let bs e -> Let <$> exprMap f bs <*> f e
    Case s ty w alts ->
        (\s' alts' -> Case s' ty w alts')
            <$> f s
            <*> sequenceA [ (,,) p bs <$> f e | (p,bs,e) <- alts ]
    Cast e co -> (`Cast` co) <$> f e
    Tick tk e -> Tick tk <$> f e
    Type{} -> pure t
    Coercion{} -> pure t

