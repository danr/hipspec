{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, RecordWildCards, ViewPatterns #-}
-- | Translation from the Functional FO to PolyFOL,
-- the only thing that needs to be done is getting rid of case,
-- and translating some types.
module ToPolyFOL where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Type as T

import FunctionalFO as FO
import PolyFOL as P
import Scope

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State

-- f :: forall a . (t1 * .. * tn) -> t
-- f x = case x of
--          A a u -> e
--
-- ! [a,x,u] . (f(a,A(a,u)) = e)

data Poly v = Id v | TyFn | Proj v Int
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Env v = Env
    { env_fn      :: Poly v
    , env_tvs     :: [Poly v]
    , env_args    :: [Term (Poly v)]
    , env_constrs :: [Formula (Poly v)]
    }

-- | The scope is typed to be able to write typed quantifiers
--
-- The Env is put in a State instead of Reader because Scope wants to be a
-- reader already :(
type TrM v a = ReaderT (Scope (FOTyped (Poly v))) (State (Env v)) a

trFun :: Ord v => Function (FOTyped v) -> [Clause (Poly v)]
trFun (fmap (fmap Id) -> Function (f ::: FOType tvs args_tys res_ty) args body) =
    (`evalState` Env f tvs (map (Var . forget_type) args) []) $
    (`runReaderT` makeScope args) $ do
        cls <- map (Clause Nothing Axiom tvs) <$> trBody body
        let ty_cl = TypeSig f tvs (map trType args_tys) (trType res_ty)
        return (ty_cl:cls)

trBody :: Ord v => Body (FOTyped (Poly v)) -> TrM v [Formula (Poly v)]
trBody b0 = case b0 of
    Case e alts0 -> do
        let (m_def,alts) = partitionAlts alts0
        lhs <- trExpr e
        dres <- case m_def of
            Nothing -> return []
            Just b  -> foldr insertConstraint
                (trBody b) [ lhs =/= P.Lit i | (p,_) <- alts, let LitPat i _ = p ]
        res <- forM alts $ \ (p,b) -> case p of
            LitPat i _ -> insertConstraint (lhs === P.Lit i) (trBody b)
            ConPat c tys args -> extendScope args $ do
                let var x = FO.Apply x [] []
                rhs <- trExpr (FO.Apply c tys (map var args))
                insertConstraint (lhs === rhs) (trBody b)
            Default -> error "ToPolyFOL.trBody: duplicate Defaults"
        return (dres ++ concat res)
    Body e -> do
        lhs <- trLhs
        rhs <- trExpr e
        scope <- getScope
        let scope' = [ (x,trType t) | x ::: FOType [] [] t <- scope ]
        constrs <- gets env_constrs
        return [forAlls scope' (constrs ===> lhs === rhs)]

insertConstraint :: Ord v => Formula (Poly v) -> TrM v a -> TrM v a
insertConstraint phi = case phi of
    TOp Equal (Var x) tm ->
        removeFromScope (x ::: error "ToPolyFOL.insertConstraint remove type") .
        locally (\ e ->
            e { env_args = map (tm // x) (env_args e) })
    _ -> locally $ \ e ->
            e { env_constrs = phi : env_constrs e }

locally :: (Env v -> Env v) -> TrM v a -> TrM v a
locally f m = do
    s <- get
    modify f
    r <- m
    put s
    return r

trLhs :: TrM v (Term (Poly v))
trLhs = do
    Env{..} <- get
    return (P.Apply env_fn (map TyVar env_tvs) env_args)

trType :: T.Type (Poly v) -> Type (Poly v)
trType t0 = case t0 of
    T.ArrTy t1 t2 -> TyCon TyFn [trType t1,trType t2]
    T.TyVar x     -> TyVar x
    T.TyCon tc ts -> TyCon tc (map trType ts)
    T.Forall{}    -> error "ToPolyFOL.trType on Forall"
    T.Star        -> Type

trExpr :: Ord v => Expr (FOTyped (Poly v)) -> TrM v (Term (Poly v))
trExpr = go . fmap forget_type
  where
    go e0 = case e0 of
        FO.Apply f as ts -> do
            b <- inScope (f ::: error "ToPolyFOL.trExpr: type in scope lookup")
            if b
                then do
                    let [] = as
                        [] = ts
                    return (Var f)
                else do
                    P.Apply f (map trType as) <$> mapM go ts
        FO.Lit x _ -> return (P.Lit x)

