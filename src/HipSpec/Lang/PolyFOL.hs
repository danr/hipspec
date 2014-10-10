{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, RecordWildCards #-}
{-# LANGUAGE ExplicitForAll, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-

Type signatures and formulae have a list of top-level quantified
type variables. They have type * (or $tType in tff1).

Formula example:

    forall (a : *) (b : *)
    -- ^ type quantification
    forall (f : Fn(a,b)) (x : a) (xs : List(a))
    -- ^ (ordinary) value quantification
    map(a,b,f,cons(a,x,xs)) = cons(b,app(a,b,f,x),map(a,b,f,xs))

Type signature example:

    forall (a : *) (b : *)
    map : (Fn(a,b) * List(a)) -> List(b)

-}
module HipSpec.Lang.PolyFOL
    ( module HipSpec.Lang.PolyFOL
    , module HipSpec.Lang.PolyFOL.Types
    ) where

import HipSpec.Lang.PolyFOL.Types

import Data.Generics.Geniplate
import Data.Generics.Genifunctors

import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor hiding (second)

import Data.Either
import Data.Maybe

import HipSpec.Utils

import Data.Set (Set)
import qualified Data.Set as S

instanceUniverseBi  [t| forall a b . (Clause a b,Term a b) |]
instanceUniverseBi  [t| forall a b . (Clause a b,Type a b) |]
instanceTransformBi [t| forall a b . (Term a b,Term a b) |]
instanceTransformBi [t| forall a b . (Term a b,Formula a b) |]
instanceTransformBi [t| forall a b . (Type a b,Clause a b) |]
instanceTransformBi [t| forall a b . (Type a b,Formula a b) |]
instanceTransformBi [t| forall a b . (Type a b,Type a b) |]

instance Bifunctor Clause     where bimap      = bimapDefault
instance Bifoldable Clause    where bifoldMap  = bifoldMapDefault
instance Bitraversable Clause where bitraverse = $(genTraverse ''Clause)

instance Bifunctor Type     where bimap      = bimapDefault
instance Bifoldable Type    where bifoldMap  = bifoldMapDefault
instance Bitraversable Type where bitraverse = $(genTraverse ''Type)

collectFOp :: Formula a b -> Maybe (FOp,[Formula a b])
collectFOp f0@(FOp op _ _) = Just (op,go f0)
  where
    go (FOp op' f1 f2) | op == op' = go f1 ++ go f2
    go f = [f]
collectFOp _              = Nothing

{-
collectQ :: Formula a b -> Maybe (Q,([(b,Type a b)],Formula a b))
collectQ f0@(Q q _ _ _) = Just (q,go f0)
  where
    go (Q q' x t f) | q == q' = let (xs,f') = go f
                                in  ((x,t):xs,f')
    go f = ([],f)
collectQ _             = Nothing
-}

-- * Builders

infix 3 ===, =/=

(===),(=/=) :: Term a b -> Term a b -> Formula a b
(===) = TOp Equal
(=/=) = TOp Unequal

infixr 2 /\
infixr 1 \/
infixr 0 ==>, ===>, <=>

neg :: Formula a b -> Formula a b
neg f = case f of
    Q q vs a b c phi -> Q (qneg q) vs a b c (neg phi)
    TOp top t1 t2 -> TOp (tneg top) t1 t2
    Named phi s -> Named (neg phi) s
    TermNamed phi tm -> TermNamed (neg phi) tm
    DataDecl{} -> error "negation on a data declaration :("
    FOp And     f1 f2 -> FOp Or    (neg f1) (neg f2)
    FOp Or      f1 f2 -> FOp And   (neg f1) (neg f2)
    FOp Implies f1 f2 -> FOp And   f1       (neg f2)
    FOp Equiv   f1 f2 -> FOp Equiv (neg f1) f2
    Neg phi -> phi
  where
    qneg Forall = Exists
    qneg Exists = Forall

    tneg Equal = Unequal
    tneg Unequal = Equal


(/\),(\/),(==>),(<=>) :: Formula a b -> Formula a b -> Formula a b
(/\)  = FOp And
(\/)  = FOp Or
(==>) = FOp Implies
(<=>) = FOp Equiv

(===>) :: [Formula a b] -> Formula a b -> Formula a b
[] ===> psi = psi
xs ===> psi = foldr1 (/\) xs ==> psi

forAll,exists :: b -> Type a b -> Formula a b -> Formula a b
forAll v t = forAlls [(v,t)]
exists v t = existss [(v,t)]

forAlls,existss :: [(b,Type a b)] -> Formula a b -> Formula a b
forAlls [] phi = phi
forAlls vs phi = Q Forall vs Nothing Nothing Nothing phi
existss [] phi = phi
existss vs phi = Q Exists vs Nothing Nothing Nothing phi

infixl `withTrigger`
infixl `withQID`
infixl `withTQID`

withTrigger :: Formula a b -> Trigger a b -> Formula a b
q@Q{} `withTrigger` t = q { q_trigger = Just t }
phi   `withTrigger` _ = phi

withQID :: Formula a b -> QID -> Formula a b
q@Q{} `withQID` i = q { q_id = Just i }
phi   `withQID` i = phi `Named` i -- NB

withTQID :: Formula a b -> Term a b -> Formula a b
q@Q{} `withTQID` t = q { q_term_id = Just t }
phi   `withTQID` t = phi `TermNamed` t

isTySymb :: TyTrigger a -> Bool
isTySymb TySymb{} = True
isTySymb _        = False


topTmSubst :: Eq b => b -> Term a b -> Term a b -> Term a b
topTmSubst x tm tm0 = case tm0 of
    Var y | x == y -> tm
    _              -> tm0

tmSubst :: forall a b . Eq b => b -> Term a b -> Term a b -> Term a b
tmSubst x tm = transformBi (topTmSubst x tm)

fmSubst :: forall a b . Eq b => b -> Term a b -> Formula a b -> Formula a b
fmSubst x tm = transformBi (topTmSubst x tm)

fmSubsts :: forall a b . Eq b => [(b,Term a b)] -> Formula a b -> Formula a b
fmSubsts xs phi = foldr (uncurry fmSubst) phi xs

topTySubst :: Eq b => b -> Type a b -> Type a b -> Type a b
topTySubst a ty ty0 = case ty0 of
    TyVar b | a == b -> ty
    _                -> ty0

fmInst :: forall a b . Eq b => b -> Type a b -> Formula a b -> Formula a b
fmInst a ty = transformBi (topTySubst a ty)

tySubst :: (TransformBi (Type a b) t, Eq b) => b -> Type a b -> t -> t
tySubst a ty = transformBi (topTySubst a ty)

fmInsts :: Eq b => [(b,Type a b)] -> Formula a b -> Formula a b
fmInsts xs phi = foldr (uncurry fmInst) phi xs

tySubsts :: (TransformBi (Type a b) t, Eq b) => [(b,Type a b)] -> t -> t
tySubsts xs phi = foldr (uncurry tySubst) phi xs

clsDeps :: forall a b . Ord a => [Clause a b] -> (Set a,Set a)
clsDeps cls =
    (S.fromList [ tc | TyCon tc _ <- concatMap clTyUniv cls ]
    ,S.fromList [ f | Apply f _ _ <- concatMap clTmUniv cls ]
    )

clTmUniv :: Clause a b -> [Term a b]
clTmUniv = universeBi

clTyUniv :: Clause a b -> [Type a b]
clTyUniv = universeBi

fmMod :: (a -> [Type a b] -> c)
      -> (a -> [Type a b] -> [Term c b] -> Term c b)
      -> Formula a b -> Formula c b
fmMod f g = fmg
  where
    fmg fm0 = case fm0 of
        TOp op tm1 tm2 -> TOp op (tmg tm1) (tmg tm2)
        FOp op fm1 fm2 -> FOp op (fmg fm1) (fmg fm2)
        Neg fm         -> Neg (fmg fm)
        Q q bvs m_trg qid tmid fm    -> Q q (map (fmap tyg) bvs) (fmap tmg m_trg) qid (fmap tmg tmid) (fmg fm)
        fm `Named` s -> fmg fm `Named` s
        fm `TermNamed` tm -> fmg fm `TermNamed` tmg tm
        DataDecl ds fm ->
            DataDecl
                [ Data (f tc ts) []
                    [ (f c ts,
                        [ (f p ts,tyg t)
                        | (p,t) <- args
                        ])
                    | (c,args) <- cons
                    ]
                | Data tc ts cons <- ds
                ]
                (fmg fm)

    tmg tm0 = case tm0 of
        Apply x ts tms -> g x ts (map tmg tms)
        Var x          -> Var x
        Lit i          -> Lit i

    tyg = tyMod f

tyMod :: (a -> [Type a b] -> c) -> Type a b -> Type c b
tyMod f ty0 = case ty0 of
    TyCon x ts -> TyCon (f x ts) []
    TyVar x    -> TyVar x
    TType      -> TType
    Integer    -> Integer

trimDataDecls :: forall a b . (Ord a,Ord b) => [Clause a b] -> [Clause a b]
trimDataDecls cls
    = Clause
        { cl_name        = Nothing
        , cl_ty_triggers = []
        , cl_type        = Axiom
        , ty_vars        = []
        , cl_formula     = DataDecl ds' (Lit 1 === Lit 1)
        }
    : filter (not . ignore) cls'
  where
    (ds,cls') = partitionEithers (map inj cls)

    inj (Clause _ _ _ _ (DataDecl d _)) = Left d
    inj c                               = Right c

    ds' = nubSortedOn (\ (Data tc ts _) -> (tc,ts)) (concat ds)

    ignores :: Set a
    ignores = S.fromList $ concat
        [ tc : concat [ c : map fst args | (c,args) <- cons ]
        | Data tc _ cons <- ds'
        ]

    ignore :: Clause a b -> Bool
    ignore TypeSig{..} = sig_id `S.member` ignores
    ignore SortSig{..} = sig_id `S.member` ignores
    ignore _           = False

-- CVC4 cannot do declare-sort, so we change all occurences of abstract
-- types to ints
uninterpretedInts :: forall a b . Eq a => [Clause a b] -> [Clause a b]
uninterpretedInts cls0 = catMaybes
    [ case cl of
        SortSig{} -> Nothing
        _         -> Just (un cl)
    | cl <- cls0
    ]
  where
    sorts = [ i | SortSig i _ <- cls0 ]
    un = transformBi $ \ t -> case t of
      TyCon tc [] | tc `elem` sorts -> Integer :: Type a b
      _                             -> t

skolemise :: forall c v tv . (v ~ tv, Eq v) =>
    (v -> Int -> c) ->
    (tv -> Int -> c) ->
    [Clause c v] -> [Clause c v]
skolemise sk_v sk_tv = concatMap sk
  where
    sk (Clause n trg Goal tvs fm) = sk (Clause n trg Axiom tvs (neg fm))
    sk (Clause n trg Axiom tvs (Q Exists vs0 _trg _id _tm_id b)) =
        [ Clause n trg Axiom [] (tySubsts ty_su (fmSubsts v_su b)) ] ++
        [ SortSig ty 0 | (_,ty) <- tys ] ++
        [ TypeSig v [] [] t | ((_,v),t) <- vs ]
      where
        tys :: [(tv,c)]
        tys = [ (tv,sk_tv tv i) | (tv,i) <- zip tvs [0..] ]

        ty_su :: [ (tv,Type c tv) ]
        ty_su = [ (x,TyCon x' []) | (x,x') <- tys ]

        vs :: [((v,c),Type c tv)]
        vs  = [ ((v,sk_v v i),tySubsts ty_su t) | ((v,t),i) <- zip vs0 [0..] ]

        v_su :: [(v,Term c v)]
        v_su = [ (x,Apply x' [] [])  | ((x,x'),_) <- vs ]

    sk c = [ c ]

{-

Note [Simple Kinded Sorts] Every sort is simple kinded, and the
number of arguments is represented by an Int.

    0: *
    1: * -> *
    2: (* x *) -> *
    3: (* x * x *) -> *

Examples:

    Fn : (* x *) -> *
    List : * -> *

Reason:

In tff1, you cannot quantify over functions. Say you had

    data Sum k a b = Left (k a) | Right (k b)

Sum would get this type:

    tff(_, type,
        sum : (($tType > $tType) * $tType * $tType) > $tType
    ).

Then the type of the Left constructor would be:

    tff(_, type,
        left : !>[K : $tType > $tType,A : $tType,B : $tType] :
            K(A) > sum(K,A,B)
    ).

The quantification (k : * -> *) is not allowed.
This could be supported by defunctionalising the kind level too.

-}

