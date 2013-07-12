{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, RecordWildCards, ViewPatterns #-}
-- | Translation from the Functional FO to PolyFOL,
-- the only thing that needs to be done is getting rid of case,
-- and translating some types.
module ToPolyFOL where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Type as T

import qualified FunctionalFO as FO
import FunctionalFO hiding (App,Ptr)
import PolyFOL as P
import TypedScope

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State

-- f :: forall a . (t1 * .. * tn) -> t
-- f x = case x of
--          A a u -> e
--
-- ! [a,x,u] . (f(a,A(a,u)) = e)

data Poly v
    = Id v
    | TyFn
    | Ptr v
    | App
    -- | Proj v Int
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
-- reader already
type TrM v a = ReaderT (Scope v (T.Type v)) (State (Env v)) a

trFun :: Ord v => Function v -> [Clause (Poly v)]
trFun (Function f tvs args res_ty body) =
    (`evalState` Env f' tvs' args' []) $
    (`runReaderT` makeScope args) $ do
        cls <- map (Clause Nothing Axiom tvs') <$> trBody body
        let ty_cl = TypeSig f' tvs' (map (trType . snd) args) (trType res_ty)
        return (ty_cl:cls)
  where
    f'    = Id f
    tvs'  = map Id tvs
    args' = map (P.Var . Id . fst) args

trBody :: Ord v => Body v -> TrM v [Formula (Poly v)]
trBody b0 = case b0 of
    Case e alts0 -> do
        let (m_def,alts) = partitionAlts alts0
        lhs <- trExpr e

        dres <- case m_def of
            Nothing -> return []
            Just b  -> foldr insertConstraint
                (trBody b) [ lhs =/= P.Lit (get_lit p) | (p,_) <- alts ]
              where
                get_lit p = case p of
                    LitPat i -> i
                    Default  -> error "ToPolyFOL.trBody: duplicate Defaults"
                    ConPat{} -> error "ToPolyFOL.trBody: constructor with Defaults!"

        res <- forM alts $ \ (p,b) -> case p of
            LitPat i -> insertConstraint (lhs === P.Lit i) (trBody b)
            ConPat c tys args -> extendScope args $ do
                let var x = FO.Fun x [] []
                rhs <- trExpr (FO.Fun c tys (map (var . fst) args))
                insertConstraint (lhs === rhs) (trBody b)
            Default -> error "ToPolyFOL.trBody: duplicate Defaults"

        return (dres ++ concat res)

    Body e -> do
        lhs <- trLhs
        rhs <- trExpr e
        scope <- getScope
        let scope' = [ (Id x,trType t) | (x,t) <- scope ]
        constrs <- gets env_constrs
        return [forAlls scope' (constrs ===> lhs === rhs)]

insertConstraint :: Ord v => Formula (Poly v) -> TrM v a -> TrM v a
insertConstraint phi = case phi of
    TOp Equal (Var (Id x)) tm ->
        removeFromScope x .
        locally (\ e -> e { env_args = map (tm // Id x) (env_args e) })
    _ -> locally (\ e -> e { env_constrs = phi : env_constrs e })

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
    return (P.Apply env_fn (map P.TyVar env_tvs) env_args)

trType :: T.Type v -> P.Type (Poly v)
trType t0 = case t0 of
    T.ArrTy t1 t2 -> P.TyCon TyFn [trType t1,trType t2]
    T.TyVar x     -> P.TyVar (Id x)
    T.TyCon tc ts -> P.TyCon (Id tc) (map trType ts)
    T.Forall{}    -> error "ToPolyFOL.trType on Forall"
    T.Star        -> error "ToPolyFOL.trType on Star"

trExpr :: Ord v => Expr v -> TrM v (Term (Poly v))
trExpr = go
  where
    go e0 = case e0 of
        FO.Fun f ts as -> do
            b <- inScope f
            if b
                then return (Var (Id f))
                else Apply (Id f) (map trType ts) <$> mapM go as

        FO.App t1 t2 e1 e2 -> Apply App (map trType [t1,t2]) <$> mapM go [e1,e2]

        FO.Ptr f ts -> return (Apply (Ptr f) (map trType ts) [])

        FO.Lit x -> return (P.Lit x)


