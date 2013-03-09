{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module HipSpec.Trans.Theory
    ( HipSpecExtras(..)
    , setExtraDependencies
    , mktotalAxioms
    , mkDomainAxioms
    , mkResultTypeAxioms
    , bottomAxioms
    , HipSpecContent
    , HipSpecSubtheory
    , Theory(..)
    ) where

import Control.Monad

import CoreSyn
import Var
import Type
import TysPrim

import TyCon
import GHC (dataConType)

import Halo.Names
import Halo.Shared
import Halo.Subtheory
import Halo.Util
import Halo.FOL.Abstract hiding (definitions)

import HipSpec.Params

import HipSpec.Trans.Types

data HipSpecExtras
    = Lemma Int
    -- ^ Lemma with a number
    | Conjecture
    -- ^ The conjecture
    | Domain TyCon
    -- ^ Domain axiom for a data type + type predicates if finite
    {-
    | AppBottomAxioms
    -- ^ App on bottom
    -- TODO : need to do one of these for every type apped on
    -}
    | Total TyCon
    -- ^ Total (+Finite) for a data type
  deriving
    (Eq,Ord)

-- | Make axioms about total
mkTotalAxioms :: [TyCon] -> [HipSpecSubtheory]
mkTotalAxioms = mapMaybe mkTotalAxiom

mkTotalAxiom :: [TyCon] -> Maybe HipSpecSubtheory
mkTotalAxiom ty_con = do
    guard (not (isNewTyCon ty_con))
    let dcs = tyConDataCons ty_con

    fs <- forM dcs $ \ dc ->
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

    let f = neg (total bottom (TCon ty_con))

    return $ Subtheory
        { provides    = Specific (total ty_con)
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
    Data ty_con -> s { depends = (bottoms ? (Specific (total ty_con) :)) $
                                 (Specific (Domain ty_con) : depends)
                     }
    Function fn -> s { depends = Specific (ResultType fn) : depends }
    _           -> s


-- | Make axioms expressing how the domain for a data type looks like
--
--   These axioms looks like
--
--   @
--     ! [U] : (U = c_Nil | U = c_Cons(s_0_Cons(U),s_1_Cons(U)))
--   @
--


mkDomainAxioms :: Params -> [TyCon] -> [HipSpecSubtheory]
mkDomainAxioms Params{bottoms} ty_cons =

mkDomainAxiom :: Params -> TyCon -> Maybe HipSpecSubtheory
mkDomainAxiom Params{bottoms} ty_con = do

    guard (not (isNewTyCon ty_con))

    let dcs@(Left dc0:_) = map Left (tyConDataCons ty_con) ++ [Right (bottom (TCon ty_con)]

        ty  = dataConType dc0
        [u] = mkVarNamesOfType [ty]
        u'  = qvar u
        domain_formulae =
            [ forall' [u] $
                ors [ u' === apply k [proj i k u' | i <- [0..arity-1] ]
                    | dc <- dcs
                    , let (k,arity) = dcIdArity dc
                    ]
            ]

    return $ Subtheory
        { provides    = Specific (Domain ty_con)
        , depends     = []
        , description = "Domain axiom for " ++ showOutputable ty_con
        , formulae    = domain_formulae
        }


-- | Make axioms about minrec
--
--   TODO : also try with an apartness relation
mkMinRecAxioms :: [TyCon] -> [HipSpecSubtheory]
mkMinRecAxioms ty_cons =
    [ let minrec_formulae =
              [ forall' xs $ minrec kxs ==> min' xi
              | dc <- dcs
              , let (k,arity)       = dcIdArity dc
                    xs              = take arity varNames
                    kxs             = apply k (map qvar xs)
              , i <- [0..arity-1]
              -- vacuous if arity == 0
              , let xi              = qvar (xs !! i)
              ]

      in  Subtheory
              { provides    = Specific (MinRec ty_con)
              , depends     = [Specific PrimMinRec]
              , description = "minrec for " ++ showOutputable ty_con
              , formulae    = minrec_formulae
              }

    | ty_con <- ty_cons
    , let dcs = tyConDataCons ty_con
    ]

instance Show HipSpecExtras where
    show (Lemma s)       = "(Lemma " ++ show s ++ ")"
    show (Domain tc)     = "(Domain " ++ showOutputable tc ++ ")"
    show AppBottomAxioms = "AppBottomAxioms"
    show (Total tc)      = "(Total " ++ showOutputable tc ++ ")"
    show Conjecture      = "Conjecture"

instance Clausifiable HipSpecExtras where
    mkClause (Lemma n) = namedClause ("lemma_" ++ show n ++ "_") lemma
    mkClause _         = clause axiom

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras

newtype Theory = Theory { subthys :: [HipSpecSubtheory] }

