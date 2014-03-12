-- | Monomorphises the Simple language, given some initial activated
--   records. The idea is that these activation records come from
--   a monomorphised conjecture.
{-# LANGUAGE RecordWildCards, ScopedTypeVariables, PatternGuards #-}
module HipSpec.Lang.Monomorphise (monoClauses, IdInst(..)) where

import Prelude hiding (lookup)
import HipSpec.Lang.PolyFOL
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M
import Data.Map (Map)

import Data.Monoid
import Data.Maybe
import Data.List (partition)
import Control.Arrow
import Control.Monad

type Records a b = Map (Trigger a) (Set [Type a b])

empty :: Records a b
empty = M.empty

member :: (Ord a,Ord b) => (Trigger a,[Type a b]) -> Records a b -> Bool
(t,ts) `member` r = maybe False (ts `S.member`) (M.lookup t r)

(\\) :: (Ord a,Ord b) => Records a b -> Records a b -> Records a b
(\\) = M.differenceWith $ \ s1 s2 -> do
    let s' = s1 S.\\ s2
    guard (not (S.null s'))
    return s'

union :: (Ord a,Ord b) => Records a b -> Records a b -> Records a b
union = M.unionWith S.union

unions :: (Ord a,Ord b) => [Records a b] -> Records a b
unions = M.unionsWith S.union

fromList :: (Ord a,Ord b) => [(Trigger a,[Type a b])] -> Records a b
fromList = M.fromListWith S.union . map (second S.singleton)

toList :: (Ord a,Ord b) => Records a b -> [(Trigger a,[Type a b])]
toList r = [ (t,ts) | (t,s) <- M.toList r, ts <- S.toList s ]

minView :: (Ord a,Ord b) => Records a b -> Maybe ((Trigger a,[Type a b]),Records a b)
minView m = case M.minViewWithKey m of
    Just ((t,s),m') -> case S.minView s of
        Just (ts,s') -> Just ((t,ts),M.insert t s' m')
        Nothing -> minView m'
    Nothing -> Nothing

insert :: (Ord a,Ord b) => Trigger a -> [Type a b] -> Records a b -> Records a b
insert i t = M.insertWith S.union i (S.singleton t)

lookup :: (Ord a,Ord b) => Trigger a -> Records a b -> [[Type a b]]
lookup t r = maybe [] S.toList (M.lookup t r)

-- | Get the records from a clause
clauseRecs :: (Ord a,Ord b) => Clause a b -> Records a b
clauseRecs cl = fromList $
    [ (TySymb tc,ts) | TyCon tc ts  <- clTyUniv cl ] ++
    [ (Symb f,ts)    | Apply f ts _ <- clTmUniv cl ]

instClauseWith :: forall a b . Eq b => Clause a b -> [(b,Type a b)] -> Clause a b
instClauseWith cl su = case cl of
    Clause nm _trg ty _tvs fm -> Clause nm [] ty [] (fmInsts su fm)
    _ -> cl -- or error!

instClause :: forall a b . Eq b => Clause a b -> [Type a b] -> Clause a b
instClause cl ts = case cl of
    Clause{..} -> instClauseWith cl (zip ty_vars ts)
    _ -> cl

type InstMap a b = Map b (Type a b)

data Lemma a b = Lemma
    { lm_cl :: Clause a b
    -- ^ the clause
    , lm_act :: [(Trigger a,[Type a b])] -- Records a b
    -- ^ The instantiation records it requires
    , lm_eff :: Records a b
    -- ^ The effect of instantiating it
    , lm_inst :: [InstMap a b]
    -- ^ The types it has already been instantiated at
    }

-- | Stage one monomorphisation
--   1st component: monomorphically applied clauses
--   2nd component: type signatures to be monomorphised
monoClauses1 :: forall a b . (Ord a,Ord b) => [Clause a b] -> ([Clause a b],[Clause a b])
monoClauses1 cls0 = (source ++ defs ++ lemma_cls,sigs)
  where
    trg_pred p Clause{..} = p cl_ty_triggers
    trg_pred _ _          = False
    (source,other)        = partition (trg_pred (Source `elem`)) cls0
    (defs_poly,rest)      = partition (trg_pred (not . null))    other
    (lem_cls,sigs)        = partition (trg_pred (const True))    rest

    mono = mkMono defs_poly

    (defs,def_irs) = mono empty (unions (map clauseRecs source))

    lemmas :: [Lemma a b]
    lemmas =
        [ Lemma cl (toList recs) (snd (mono empty recs)) []
        | cl <- lem_cls
        , let recs = clauseRecs cl
        ]

    go :: Bool -> [Lemma a b] -> [Lemma a b] -> Records a b -> [Clause a b]
    go False [] _   _   = []
    go True  [] acc irs = go False acc [] irs
    go b (l:ls) acc irs = case new of
        []        -> go b ls (l:acc) irs
        (l',cl):_ ->
            let (cls,irs') = mono irs (clauseRecs cl)
            in  cl:cls ++ go True (l':ls) acc irs'
      where
        new = catMaybes
            [ instLemma l im irs
            | im <- possibleInsts l irs
            ]

    lemma_cls = go False lemmas [] def_irs

instLemma :: (Ord a,Ord b)
          => Lemma a b   {- ^ lemma to maybe instantiate -}
          -> InstMap a b {- ^ type to instantiate it at -}
          -> Records a b {- ^ instantiated records so far -}
          -> Maybe (Lemma a b,Clause a b)
                         {- Just (l,r,c) :
                                l: Lemma with new info
                                c: The clause that got instantiated -}
instLemma l@Lemma{..} im rs
    -- Instantiate lemmas as long as they don't trigger new
    -- types to be instantiated
    | and
        [ (t,map (tySubsts (M.toList im)) ts) `member` rs
        | (t,ts) <- takeWhile (isTySymb . fst) (toList lm_eff)
        ]
      -- and we haven't instantiated it before
      && im `notElem` lm_inst
      -- and all type variables are assigned
      && all (`M.member` im) (ty_vars lm_cl)

    = Just
        ( l { lm_inst = im : lm_inst }
        , instClauseWith lm_cl (M.toList im)
        )

    | otherwise = Nothing

-- | Possible instantiations of a lemma given some instantiation records
possibleInsts :: (Ord a,Ord b) => Lemma a b -> Records a b -> [InstMap a b]
possibleInsts Lemma{..} rs = go lm_act
  where
    go []            = [M.empty]
    go ((trg,ts):xs) =
        [ m1 `M.union` m2
        | m1 <- M.empty : mapMaybe (tyInsts ts) (lookup trg rs)
        , m2 <- go xs
        , compatible m1 m2
        ]

tyInst :: (Ord a,Ord b)
       => Type a b {- ^ with type variables -}
       -> Type a b {- ^ without -}
       -> Maybe (InstMap a b)
tyInst (TyVar x)    t                     = Just (M.singleton x t)
tyInst (TyCon u us) (TyCon v vs) | u == v = tyInsts us vs
tyInst TType        TType                 = Just M.empty
tyInst Integer      Integer               = Just M.empty
tyInst _            _                     = Nothing

tyInsts :: (Ord a,Ord b) => [Type a b] -> [Type a b] -> Maybe (InstMap a b)
tyInsts (u:us) (v:vs) = do
    m1 <- tyInst u v
    m2 <- tyInsts us vs
    guard (compatible m1 m2)
    return (m1 `M.union` m2)
tyInsts [] [] = Just M.empty
tyInsts _  _  = Nothing

compatible :: (Ord a,Ord b) => InstMap a b -> InstMap a b -> Bool
compatible a b = oneway a b && oneway b a
  where
    oneway p q = and [ maybe True (== v) (M.lookup k q) | (k,v) <- M.toList p ]

mkMono :: forall a b . (Ord a,Ord b)
       => [Clause a b]
       -> Records a b                -- ^ Initial, already instantiated records
       -> Records a b                -- ^ New record queue
       -> ([Clause a b],Records a b) -- ^ Instantiated clauses and final records
mkMono cls0 irs0 q0 = go irs0 (q0 \\ irs0)
  where
    -- Since some clauses are activated by either of many triggers,
    -- we let one of them instantiate the clause, and the other ones just
    -- retrigger with the major pattern
    trg_targets :: Map (Trigger a) ([Clause a b],[Trigger a])
    trg_targets = M.fromListWith mappend $
        [ (trg,([cl],trgs))
        | cl <- cls0
        , let trg:trgs = cl_ty_triggers cl
        ]

    go :: Records a b
       -> Records a b
       -- ^ (invariant: no overlap)
       -> ([Clause a b],Records a b)
    go irs q = case minView q of
        Nothing -> ([],irs)
        Just ((trg,ts),q') -> case M.lookup trg trg_targets of
            Nothing            -> go irs q'
            Just (cls,retrigs) ->
                let cls' = map (`instClause` ts) cls
                    rtr  = fromList (zip retrigs (repeat ts))
                    irs' = insert trg ts irs
                    recs = (unions (map clauseRecs cls') `union` rtr) \\ irs'
                in  first (cls' ++) (go irs' (q' `union` recs))

data IdInst a b = IdInst a [Type a b]
  deriving (Eq,Ord,Show)

-- | Second pass monomorphisation: remove all type applications and change
--   the identifier names instead
monoClauses2 :: (Ord a,Ord b) => ([Clause a b],[Clause a b]) -> [Clause (IdInst a b) b]
monoClauses2 (cls,sigs) = map (`SortSig` 0) (S.toList sorts) ++ ty_sigs ++ cls'
  where
    cls' =
        [ Clause
            { cl_name        = cl_name cl
            , cl_ty_triggers = []
            , cl_type        = cl_type cl
            , ty_vars        = []
            , cl_formula     = fmMod tyCon apply (cl_formula cl)
            }
        | cl <- cls
        ]

    tyCon f ts = TyCon (IdInst f ts) []
    apply f ts = Apply (IdInst f ts) []

    (sorts1,ty_apps) = clsDeps cls'


    sig_map = M.fromList [ (f,(tvs,args,res)) | TypeSig f tvs args res <- sigs ]

    ty_sigs =
       [ TypeSig f' [] args' res'
       | f'@(IdInst f ts) <- S.toList ty_apps
       , Just (tvs,args,res) <- [M.lookup f sig_map]
       , let su = tyMod tyCon . tySubsts (zip tvs ts)
             args' = map su args
             res'  = su res
       ]

    (sorts2,_) = clsDeps ty_sigs

    sorts = sorts1 `S.union` sorts2

-- | Monomorphise clauses
monoClauses :: (Ord a,Ord b) => [Clause a b] -> [Clause (IdInst a b) b]
monoClauses = monoClauses2 . monoClauses1

