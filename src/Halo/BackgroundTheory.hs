{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-

    Background theory:

        * Data type projections and discriminators

        * Pointers to data constructors

-}
module Halo.BackgroundTheory (backgroundTheory) where

import TyCon
import Var
import Type

import Halo.FOL.Abstract

import Halo.Conf
import Halo.Names
import Halo.Pointer
import Halo.Shared
import Halo.Util
import Halo.Subtheory
import Halo.MonoType

import Data.List
import Data.Maybe

-- | Makes the background theory with these settings and data types
backgroundTheory :: HaloConf -> [TyCon] -> [Subtheory s]
backgroundTheory halo_conf = concat . mapMaybe (tyConSubtheory halo_conf)

-- | Makes the projections, discrimination and pointer axioms for a data type
tyConSubtheory :: HaloConf -> TyCon -> Maybe [Subtheory s]
tyConSubtheory HaloConf{use_bottom} ty_con
    | isNewTyCon ty_con = do

        return $ [calculateDeps subtheory
            { provides     = Data ty_con
            , depends      = []
            , description  = "Abstract newtype " ++ showOutputable ty_con
            , formulae     = []
            , sortdecls    = [ty_con]
            }]

    | otherwise = do

        cons <- (++ [ Nothing | use_bottom ]) <$> sequence
            [ Just . (,,) k arg_types <$> mapM monoType arg_types
            | dc <- tyConDataCons ty_con
            , let (k,arg_types) = dcIdArgTypes dc
            ]

        let rm_mid (a,_,c) = (a,c)

            ty_con_monoty = TCon ty_con

            projections :: [Formula']
            projections =
                [ forall' (zip xs monotys) $ proj i k kxs === xi
                | Just (k,tys,monotys) <- cons
                , let xs  = mkVarNamesOfType tys
                      kxs = apply k (map qvar xs)
                , i <- [0..length xs-1]
                , let xi = qvar (xs !! i)
                ]

            discrims :: [Formula']
            discrims =
                [ forall' (lvars ++ rvars) (lhs =/= rhs)
                | (j,ks) <- zip cons (drop 1 (tails cons))
                , let (lhs,lvars) = make_side 0 j
                , k <- ks
                , let (rhs,rvars) = make_side (length lvars) k
                ]
              where
                make_side :: Int -> Maybe (Var,[Type],[MonoType']) -> (Term',[(Var,MonoType')])
                make_side offset m_k = case m_k of
                    Nothing -> (bottom ty_con_monoty,[])
                    Just (k,arg_tys,arg_monotys) ->
                        (apply k (map qvar xs),zip xs arg_monotys)
                      where
                        xs = mkVarNamesOfTypeWithOffset offset arg_tys

            domain :: Formula'
            domain = forall' [(u,ty_con_monoty)] $ ors $
                [ u' === apply k [proj i k u' | i <- [0..arity-1] ]
                | Just (k,tys,_monotys) <- cons
                , let arity = length tys
                ] ++
                [ u' === bottom ty_con_monoty | use_bottom ]
              where
                [u] = mkVarNamesOfType [mkTyConTy ty_con]
                u'  = qvar u

        -- Pointers, to each non-nullary constructor k
        pointer_subthys <- sequence
            [ fmap (\ s -> s { depends = [Data ty_con] }) (mkPtr k)
            | Just (k,tys,_) <- cons
            , length tys > 0
            ]

        return $ calculateDeps subtheory
            { provides     = Data ty_con
            , depends      = []
            , description  = showOutputable ty_con
            , formulae     = domain : discrims ++ projections
            , datadecls    = [(ty_con,map (fmap rm_mid) cons)]
            }
            : pointer_subthys

{-
dummyAny :: Subtheory s
dummyAny = mkDummySubtheory (Data anyTyCon)
-}

