{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module HipSpec.Trans.Theory
    ( HipSpecExtras(..)
    , setExtraDependencies
    , mkTotalAxioms
    , mkTotalAxiom
    , mkAppThy
    , HipSpecContent
    , HipSpecSubtheory
    , Theory
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
    | AppBottomAxioms MonoType'
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

mkTotalAxiom :: (Applicative m,Monad m) => TyCon -> m HipSpecSubtheory
mkTotalAxiom ty_con
    | isNewTyCon ty_con = do

        let [x] = mkVarNamesOfType [mkTyConTy ty_con]

        frmla <- foralls varMonoType (total (TCon ty_con) (qvar x) <=>
                                        qvar x =/= bottom (TCon ty_con))

        return $ calculateDeps subtheory
            { provides     = Specific (TotalThy ty_con)
            , depends      = [Data ty_con]
            , clauses      =
                [ comment $ "Total for abstract newtype " ++ showOutputable ty_con
                , axiom frmla
                , totalSig (TCon ty_con)
                ]
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
            , depends     = [Data ty_con]
            , clauses     =
                [ comment $ "Totality for " ++ showOutputable ty_con
                , totalSig (TCon ty_con)
                ] ++ axioms (f:fs)
            }


-- | Mainly interesting if bottoms are used, otherwise this is only
--   a type signature.
mkAppThy :: Params -> MonoType' -> HipSpecSubtheory
mkAppThy _          TCon{}          = error "Trying to make app thy on TCon"
mkAppThy Params{..} ty@(TArr t1 t2) = calculateDeps subtheory
    { provides    = AppThy ty
    , depends     =
        let dep (TCon ty_con) = Data ty_con
            dep t@TArr{}      = AppThy t
        in  nubSorted [dep t1,dep t2]
    , clauses    =
        [ sortSig ty
        , typeSig (AnApp ty) [ty,t1] t2 ] ++

        concat
            [ let f,x :: Var
                  f:x:_ = untypedVarNames

                  qf,qx :: Term'
                  [qf,qx] = map qvar [f,x]
                  -- TODO: if bottom of a function type is used, add that app theory
              in  [ typeSig (ABottom ty) [] ty
                  , totalSig ty
                  , axiom $ forall' [(x,t1)] (app ty (bottom ty) qx === bottom t2)
                  , axiom $ forall' [(f,ty)] (total ty qf <=>
                      forall' [(x,t1)] (total t1 qx ==> total t2 (app ty qf qx)))
                  ]
            | bottoms
            ]
    }
  where

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

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras

type Theory = [HipSpecSubtheory]

