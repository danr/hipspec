{-# LANGUAGE RecordWildCards #-}
{-

    Background theory:

        * Data type projections and discriminators

        * Pointers to data constructors

        * Min on app

        * Extensional equality

-}
module Halo.BackgroundTheory ( backgroundTheory ) where

import Outputable
import TyCon
import Type
import TysPrim

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
            [ foralls  $ [min' kxs,min' xi] ===> proj i k kxs === xi
            -- I think maybe this should just be min' kxs ==>
            | dc <- dcs
            , let (k,arity) = dcIdArity dc
                  xs        = take arity varNames
                  kxs       = apply k (map qvar xs)
            , i <- [0..arity-1]
            , let xi        = qvar (xs !! i)
            ]

     -- Discriminations,  for j,k in the same TyCon + unr/bad, make j and k disjoint

        discrims =
            [ foralls $ min' lhs : [ min' rhs | need_min ] ===> lhs =/= rhs

            | let tagged_dcs
                    = [ (True,dc) | dc <- dcs ] ++
                      [ (False,prim_con)
                      | unr_and_bad
                      , prim_con <- [primCon BAD,primCon UNR] ]

            , (j_dc,ks) <- zip dcs (drop 1 (tails tagged_dcs))

            , (need_min,k_dc) <- ks

            , let (j,j_arity)     = dcIdArity j_dc
                  (k,k_arity)     = dcIdArity k_dc

                  (j_args,k_args) = second (take k_arity) (splitAt j_arity varNames)

                  lhs             = apply j (map qvar j_args)
                  rhs             = apply k (map qvar k_args)
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
    , isAlgTyCon ty_con
    , DataTyCon dcs _ <- [algTyConRhs ty_con]
    ]

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
