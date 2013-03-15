{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module HipSpec.Trans.Theory
    ( HipSpecExtras(..)
    , setExtraDependencies
    , mkTotalAxioms
    , HipSpecContent
    , HipSpecSubtheory
    , Theory(..)
    , module Halo.Subtheory
    ) where

import Control.Monad

import Var
import Type
import TysPrim

import TyCon

import Halo.Names
import Halo.Shared
import Halo.Subtheory
import Halo.Util
import Halo.MonoType
import Halo.FOL.Abstract hiding (definitions)
import Data.Maybe

import HipSpec.Params

data HipSpecExtras
    = Lemma Int
    -- ^ Lemma with a number
    | Conjecture
    -- ^ The conjecture
    {-
    | AppBottomAxioms
    -- ^ App on bottom
    -- TODO : need to do one of these for every type apped on
    -}
    | TotalThy TyCon
    -- ^ Total (+Finite) for a data type
  deriving
    (Eq,Ord)

-- | Make axioms about total
mkTotalAxioms :: [TyCon] -> [HipSpecSubtheory]
mkTotalAxioms = mapMaybe mkTotalAxiom

mkTotalAxiom :: TyCon -> Maybe HipSpecSubtheory
mkTotalAxiom ty_con
    | isNewTyCon ty_con = do

        let [x] = mkVarNamesOfType [mkTyConTy ty_con]

        frmla <- foralls varMonoType (total (TCon ty_con) (qvar x) <=>
                                        qvar x =/= bottom (TCon ty_con))

        return $ calculateDeps subtheory
            { provides     = Specific (TotalThy ty_con)
            , depends      = []
            , description  = "Total for abstract newtype " ++ showOutputable ty_con
            , formulae     = [frmla]
            , sortdecls    = []
            }

    | otherwise = do

        let dcs = tyConDataCons ty_con

        fs <- forM dcs $ \ dc -> do
            let (k,arg_types) = dcIdArgTypes dc
                xbar          = mkVarNamesOfType arg_types
                kxbar         = apply k (map qvar xbar)
                is_primitive  = (`eqType` intPrimTy) . varType

            left <- sequence
                [ (`total` qvar x) <$> varMonoType x
                | x <- xbar
                , not (is_primitive x)
                ]

            foralls varMonoType $ left <==> total (TCon ty_con) kxbar

        let f = neg (total (TCon ty_con) (bottom (TCon ty_con)))

        return $ calculateDeps subtheory
            { provides    = Specific (TotalThy ty_con)
            , depends     = []
            , description = "total " ++ showOutputable ty_con
            , formulae    = f:fs
            }


{-
            { provides    = Specific AppBottomAxioms
            , depends     = []
            , description = "Axioms for app on bottom"
            , formulae    =
                [ forall' [x] $ app bot x' === bot
                , forall' [f] $ total f' <==>
                    forall' [x] (total x' ==> total (app f' x'))
                ]
            }
-}

-- | Make data types depend on Domain axioms, and MinRec axioms if min is used.
--   Make functions depend on finite result type axioms.
setExtraDependencies :: Params -> HipSpecSubtheory -> HipSpecSubtheory
setExtraDependencies Params{..} s@(Subtheory{..}) = case provides of
    Data ty_con -> s { depends = (bottoms ? (Specific (TotalThy ty_con) :)) depends }
    _           -> s

instance Show HipSpecExtras where
    show (Lemma s)       = "(Lemma " ++ show s ++ ")"
    show (TotalThy tc)   = "(Total " ++ showOutputable tc ++ ")"
    show Conjecture      = "Conjecture"

instance Clausifiable HipSpecExtras where
    mkClause (Lemma n) = namedClause ("lemma_" ++ show n ++ "_") lemma
    mkClause _         = clause axiom

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras

newtype Theory = Theory { subthys :: [HipSpecSubtheory] }

