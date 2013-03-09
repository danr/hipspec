{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-

    Background theory:

        * Data type projections and discriminators

        * Pointers to data constructors

-}
module Halo.BackgroundTheory (backgroundTheory) where

import TyCon
import DataCon

import Halo.FOL.Abstract

import Halo.Conf
import Halo.Names
import Halo.Pointer
import Halo.Shared
import Halo.Subtheory
import Halo.MonoType

import Data.List
import Data.Maybe

import Control.Monad

-- | Makes the background theory with these settings and data types
backgroundTheory :: HaloConf -> [TyCon] -> [Subtheory s]
backgroundTheory halo_conf = concat . mapMaybe (tyConSubtheory halo_conf)

-- | Makes the projections, discrimination and pointer axioms for a data type
tyConSubtheory :: HaloConf -> TyCon -> Maybe [Subtheory s]
tyConSubtheory HaloConf{use_bottom} ty_con = do

    -- newtypes are abstract for us right now
    guard (not (isNewTyCon ty_con))

    let dcs = tyConDataCons ty_con

    cons <- (++ [ (Nothing,[]) | use_bottom ]) <$> sequence
        [ (,) (Just k) <$> mapM monoType arg_types
        | dc <- dcs
        , let (k,arg_types) = dcIdArgTypes dc
        ]

    -- Projections, for each constructor k
    projections <- sequence
        [ foralls varMonoType $ proj i k kxs === xi
        | dc <- dcs
        , let (k,arg_types) = dcIdArgTypes dc
              xs            = mkVarNamesOfType arg_types
              kxs           = apply k (map qvar xs)
        , i <- [0..length arg_types-1]
        , let xi = qvar (xs !! i)
        ]

     -- Discriminations,
     -- for j,k + bottom, make j and k disjoint

    let tagged_dcs :: [Either DataCon Term']
        tagged_dcs = [ Left dc | dc <- dcs ] ++
                     [ Right (bottom (TCon ty_con)) | use_bottom ]

        make_side :: Int -> DataCon -> (Term',Int)
        make_side offset dc =
            let (k,arg_tys) = dcIdArgTypes dc
                args = mkVarNamesOfTypeWithOffset offset arg_tys
            in  (apply k (map qvar args),length arg_tys)

    discrims <- sequence

        [ foralls varMonoType $ lhs =/= rhs
        | (j_dc,ks) <- zip dcs (drop 1 (tails tagged_dcs))
        , let (lhs,offset) = make_side 0 j_dc
        , other <- ks
        , let rhs = case other of
                        Left k_dc     -> fst (make_side offset k_dc)
                        Right bot_rhs -> bot_rhs
        ]

    domain <-

    -- Pointers, to each non-nullary constructor k
    pointer_subthys <- sequence
        [ fmap (\ s -> s { depends = [Data ty_con] }) (mkPtr k)
        | dc <- dcs
        , let (k,arity) = dcIdArity dc
        , arity > 0
        ]

    return $ Subtheory
        { provides    = Data ty_con
        , depends     = []
        , description = showOutputable ty_con
        , formulae    = projections ++ discrims
        }
        : pointer_subthys

{-
dummyAny :: Subtheory s
dummyAny = mkDummySubtheory (Data anyTyCon)
-}

