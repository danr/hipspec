{-# LANGUAGE RecordWildCards, DeriveFunctor #-}
{-

    A subtheory is something from Haskell that can be translated to
    FOL if it is necessary. If you know what functions are important
    for a specific goal, you can trim a grand theory with Halo.Trim.

    The different kinds of subtheories are:

        * Discrimination and projection axioms for a data type

            from Halo.BackgroundTheory

        * Function definition

            from Halo.Binds

        * A pointer definition

            from Halo.Pointer, used in both BackgroundTheory (for
            constructor pointers), and in Binds (for function pointers)

        * Extensional equality

        * Specific

            Something specific to the user of the Halo library.
            Examples: in Contracts the axiomatisations of crash-freeness,
            in HipSpec, we make a subtheory for each lemma.

-}
module Halo.Subtheory where

import Halo.Shared
import Halo.Util
import Halo.FOL.Abstract
import Halo.MonoType
import Halo.FOL.LineariseSMT
import Halo.FOL.Operations

import Id
import DataCon
import TyCon

import Data.Function

data Content s
    = Data TyCon
    -- ^ Discrimination, domain and projection axioms for a data type
    | Function Var
    -- ^ A definition of a function
    | Pointer Var
    -- ^ The pointer to a function definition or constructor
    | AppThy MonoType'
    -- ^ App used on this type
    | Specific s
    -- ^ User specific content
  deriving (Eq,Ord,Functor)

mapFunctionContent :: (Var -> Var) -> Content s -> Content s
mapFunctionContent f (Function v) = Function (f v)
mapFunctionContent _ c            = c

pointers :: [Var] -> [Content s]
pointers = map Pointer

functions :: [Var] -> [Content s]
functions = map Function

datas :: [TyCon] -> [Content s]
datas = map Data

baseContentShow :: Content s -> String
baseContentShow c = case c of
    Function v          -> "(Function " ++ showOutputable v ++ ")"
    Pointer v           -> "(Pointer " ++ showOutputable v ++ ")"
    Data tc             -> "(Data " ++ showOutputable tc ++ ")"
    AppThy _t           -> "(AppThy " ++ "..." ++ ")"
    Specific _          -> "(Unknow Specific)"

instance Show s => Show (Content s) where
    show c = case c of
        Specific s -> "(Specific " ++ show s ++ ")"
        _          -> baseContentShow c

-- | A subtheory
--
--   Provides some content, and can also depend upon other content.
--
--   The provides fields should be unique when assembling a grand theory,
--   Eq and Ord instances are on this field.
--
--   There is an optional description which is translated to a TPTP
--   comment for debug output.
data Subtheory s = Subtheory
    { provides     :: Content s
    -- ^ Content defined
    , depends      :: [Content s]
    -- ^ Content depending upon
    , clauses      :: [Clause']
    -- ^ Formulae in this subtheory
    , datadecls    :: [(TyCon,[(Var,[MonoType'])])]
    -- ^ Data declarations from this subtheory.
    --   This could be used in the SMT lineariser,
    --   but that assumes finite types
    }
  deriving Functor

instance Eq s => Eq (Subtheory s) where
    (==) = (==) `on` provides

instance Ord s => Ord (Subtheory s) where
    compare = compare `on` provides

-- | A yet to become subtheory, but with empty typedecls, datadecls and used_apps.
subtheory :: Subtheory s
subtheory = Subtheory
    { provides    = error "subtheory: please fill in provides"
    , depends     = []
    , clauses     = error "subtheory: please fill in clauses"
    , datadecls   = []
    }

-- Calculates dependecies (to app, pointer, data and function)
calculateDeps :: Ord s => Subtheory s -> Subtheory s
calculateDeps s@Subtheory{..} = s
    { depends = nubSorted $ depends
                    ++ map (Pointer . fst) (ptrsUsed clauses)
                    ++ map AppThy (appsUsed clauses)
                    ++ map Function (funsUsed clauses)
                    ++ map idToContent (ctorsUsed clauses)
                    ++ map type_thy (totalsUsed clauses)
                    ++ map type_thy (bottomsUsed clauses)
                    ++ map type_thy (tysUsed clauses)
    }
  where
    type_thy (TCon ty_con) = Data ty_con
    type_thy ty@TArr{}     = AppThy ty

instance Show s => Show (Subtheory s) where
    show (Subtheory{..}) =
        "Subtheory\n  { content=" ++ show provides
              ++ "\n  , depends=" ++ show depends
              ++ "\n  , clauses=\n" ++ unlines (map (sexpr 4 . linClause) clauses)
              ++ "\n  }"

mkDummySubtheory :: Content s -> Subtheory s
mkDummySubtheory c = subtheory
    { provides    = c
    , depends     = []
    , clauses     = []
    }

idToContent :: Id -> Content s
idToContent i = case isDataConId_maybe i of
    Just dc -> Data (dataConTyCon dc)
    Nothing -> Function i


