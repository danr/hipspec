{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-

    Background theory:

        * Data type projections and discriminators

        * Pointers to data constructors

        * Min on app

        * Extensional equality

-}
module Halo.BackgroundTheory
    ( backgroundTheory
    , makeDisjoint
    , Disjoint(..)
    ) where

import Outputable
import TyCon
import Type
import TysPrim
import Var

import Halo.FOL.Abstract

import Halo.Conf
import Halo.Names
import Halo.Pointer
import Halo.PrimCon
import Halo.Shared
import Halo.Subtheory
import Halo.Util

import Data.List

-- | Makes the background theory with these settings and data types
backgroundTheory :: HaloConf -> [TyCon] -> [Subtheory s]
backgroundTheory halo_conf ty_cons
    = extEq : appOnMin : dummyAny
    : tyConSubtheories halo_conf ty_cons

tyConSubtheories :: HaloConf -> [TyCon] -> [Subtheory s]
tyConSubtheories halo_conf@HaloConf{..} ty_cons = concat
    [ -- Projections, for each constructor k
    let projections =
            [ foralls  $ [min' kxs {- ,min' xi -} ] ===> proj i k kxs === xi
            -- Used to also have min' xi ==>
            | dc <- dcs
            , let (k,arg_types) = dcIdArgTypes dc
                  xs            = zipWith setVarType varNames arg_types
                  kxs           = apply k (map qvar xs)
            , i <- [0..length arg_types-1]
            , let xi = qvar (xs !! i)
            ]

     -- Discriminations,  for j,k in the same TyCon + unr/bad, make j and k disjoint

        discrims

            -- (but for newtypes just say k(x) = x)
            | isNewTyCon ty_con =
                [ forall' [u] (apply k [u'] === u')
                | dc <- dcs
                , let (k,[t]) = dcIdArgTypes dc
                      u = setVarType x t
                      u' = qvar u
                ]

            | otherwise =

                [ makeDisjoint halo_conf j k
                | let disjoints = map fromTag $
                          [ (True,dc) | dc <- dcs ] ++
                          [ (False,prim_con)
                          | unr_and_bad
                          , prim_con <- [primCon BAD,primCon UNR] ]

                      fromTag (min_guard,dc) = Disjoint{..}
                        where
                          (symbol,arg_types) = dcIdArgTypes dc
                          is_ptr             = False

                , (j,ks) <- zip disjoints (drop 1 (tails disjoints))
                , k <- ks
                , not (symbol j == primId BAD && symbol k == primId UNR)
                ]

     -- Pointers, to each non-nullary constructor k

        pointer_subthys =
            [ (mkPtr halo_conf k arity) { depends = [Data ty_con] }
            | dc <- dcs
            , let (k,arity) = dcIdArity dc
            , arity > 0
            ]

    in  Subtheory
            { provides    = Data ty_con
            , depends     = []
            , description = showSDoc (pprSourceTyCon ty_con)
            , formulae    = projections ++ discrims
            }
        : pointer_subthys

    | ty_con <- ty_cons
    , let dcs = tyConDataCons ty_con
    ]

data Disjoint = Disjoint
    { symbol            :: Var
    , arg_types         :: [Type]
    , is_ptr, min_guard :: Bool
    }

-- | Makes these two entries disjoint
makeDisjoint :: HaloConf -> Disjoint -> Disjoint -> Formula'
makeDisjoint HaloConf{or_discr} dj dk =
      foralls $ ([ min' lhs | j_min ] ++ [ min' rhs | k_min ])
                `implies` (lhs =/= rhs)
  where
    Disjoint j j_arg_types j_ptr j_min = dj
    Disjoint k k_arg_types k_ptr k_min = dk

    k_arity = length k_arg_types
    j_arity = length j_arg_types

    [] `implies` phi = phi
    xs `implies` phi = (if or_discr then ors else ands) xs ==> phi

    (j_args0,k_args0) = second (take k_arity) (splitAt j_arity varNames)
    j_args = zipWith setVarType j_args0 j_arg_types
    k_args = zipWith setVarType k_args0 k_arg_types

    mkSide i i_args i_ptr
        | i_ptr     = ptr i
        | otherwise = apply i (map qvar i_args)

    lhs  = mkSide j j_args j_ptr
    rhs  = mkSide k k_args k_ptr

appOnMin :: Subtheory s
appOnMin = Subtheory
    { provides    = AppOnMin
    , depends     = []
    , description = "App on min"
    , formulae    = [forall' [f,x] $ min' (app f' x') ==> min' f']
    }

extEq :: Subtheory s
extEq = Subtheory
    { provides    = ExtensionalEquality
    , depends     = []
    , description = "Extensional equality"
    , formulae    = return $
         forall' [f,g] (forall' [x] (app f' x' === app g' x') ==> f' === g')
    }

dummyAny :: Subtheory s
dummyAny = mkDummySubtheory (Data anyTyCon)
