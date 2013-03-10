{-# LANGUAGE RecordWildCards #-}
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
import Halo.Monad
import Halo.FOL.Abstract

import Var
import TyCon

import Data.Function

data Content s
    = Data TyCon
    -- ^ Discrimination, domain and projection axioms for a data type
    | Function Name
    -- ^ A definition of a function
    | Pointer Name
    -- ^ The pointer to a function definition or constructor
    | Specific s
    -- ^ User specific content
  deriving (Eq,Ord)

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
    AppTheory           -> "(AppTheory)"
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
    , description  :: String
    -- ^ Commentary
    , formulae     :: [Formula']
    -- ^ Formulae in this subtheory
    , typedecls    :: [(Var,MonoType')]
    -- ^ Type declarations from this subtheory
    , datadecls    :: [(TyCon,[(Maybe Var,[MonoType'])]]
    -- ^ Data declarations from this subtheory
    }

instance Eq s => Eq (Subtheory s) where
    (==) = (==) `on` provides

instance Ord s => Ord (Subtheory s) where
    compare = compare `on` provides

-- | A yet to become subtheory, but with empty typedecls, datadecls and used_apps.
subtheory :: Subtheory s
subtheory = Subtheory
    { provides     = error "subtheory: please fill in provides"
    , depends      = error "subtheory: please fill in depends"
    , description  = error "subtheory: please fill in description"
    , formulae     = error "subtheory: please fill in formulae"
    , typedecls    = []
    , datadecls    = []
    }

instance Show s => Show (Subtheory s) where
    show subthy = "Subtheory { content=" ++ show (provides subthy)
                          ++ ", depends=" ++ show (depends subthy) ++ "}"

class Clausifiable s where
    mkClause :: s -> Formula' -> Clause'

instance Clausifiable s => Clausifiable (Content s) where
    mkClause (Specific s) = mkClause s
    mkClause Function{}   = clause definition
    mkClause _            = clause axiom

toClauses :: Clausifiable s => Subtheory s -> [Clause']
toClauses (Subtheory{..}) = commentary ++ map (mkClause provides) formulae
  where
    commentary
        | description /= "" = [comment description]
        | otherwise         = []

mkDummySubtheory :: Content s -> Subtheory s
mkDummySubtheory c = subtheory
    { provides    = c
    , depends     = []
    , description = ""
    , formulae    = []
    }

