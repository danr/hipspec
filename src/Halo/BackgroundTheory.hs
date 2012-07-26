{-# LANGUAGE RecordWildCards #-}
-- Translating data types

module Halo.BackgroundTheory ( backgroundTheory ) where

import DataCon
import Id
import Outputable
import TyCon
import Type

import Halo.FOL.Abstract

import Halo.Conf
import Halo.Names
import Halo.Pointer
import Halo.PrimCon
import Halo.Subtheory

import Control.Monad.Reader
import Data.List

-- | Makes the background theory with these settings and data types
backgroundTheory :: HaloConf -> [TyCon] -> [Subtheory s]
backgroundTheory halo_conf ty_cons
    = extEq : appOnMin
    : concatMap (\k -> k halo_conf ty_cons) [mkProjDiscrim,mkConPtrs]

mkProjDiscrim :: HaloConf -> [TyCon] -> [Subtheory s]
mkProjDiscrim HaloConf{..} ty_cons =
   [ -- Projections
     let projections =
            [ forall' xs $ [min' kxs,min' xi] ===> proj i k kxs === xi
            | c <- cons
            , let k               = dataConWorkId c
                  (_,_,ty_args,_) = dataConSig c
                  arity           = length ty_args
                  xs              = take arity varNames
                  kxs             = apply k (map qvar xs)
            , i <- [0..arity-1]
            , let xi              = qvar (xs !! i)
            ]

     -- Discriminations

         discrims =
            [ forall' (names ++ uneq_names) $
                      min' lhs : [ min' rhs | need_min ] ===> lhs =/= rhs
            | let allcons = map ((,) True) cons
                            ++ concat [ map ((,) False) [primCon BAD,primCon UNR] ]
            , (c,unequals) <- zip cons (drop 1 $ tails allcons)
            , (need_min,uneq_c) <- unequals
            , let data_c          = dataConWorkId c
                  (_,_,ty_args,_) = dataConSig c
                  arity           = length ty_args

                  uneq_data_c          = dataConWorkId uneq_c
                  (_,_,uneq_ty_args,_) = dataConSig uneq_c
                  uneq_arity           = length uneq_ty_args

                  names      = take arity varNames
                  uneq_names = take uneq_arity (drop arity varNames)

                  lhs    = apply data_c (map qvar names)
                  rhs    = apply uneq_data_c (map qvar uneq_names)
            ]

     in Subtheory
            { provides    = Data ty_con
            , depends     = []
            , description = showSDoc (pprSourceTyCon ty_con)
            , formulae    = projections ++ discrims
            }

   | ty_con <- ty_cons
   , let DataTyCon cons _ = algTyConRhs ty_con
   ]

-- | Make pointers to constructors
mkConPtrs :: HaloConf -> [TyCon] -> [Subtheory s]
mkConPtrs halo_conf ty_cons = do
    ty_con <- ty_cons
    let DataTyCon cons _ = algTyConRhs ty_con

    c <- cons
    let data_c          = dataConWorkId c
        (_,_,ty_args,_) = dataConSig c
        arity           = length ty_args

    guard (arity > 0)

    return $ (mkPtr halo_conf data_c arity) { depends = [Data ty_con] }

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

