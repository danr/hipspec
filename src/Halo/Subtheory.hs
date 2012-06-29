{-# LANGUAGE RecordWildCards #-}
module Halo.Subtheory where

import Halo.Util
import Halo.Shared
import Halo.FOL.Abstract hiding (Lemma)
import qualified Halo.FOL.Abstract as A

import Var
import TyCon

import Data.Function

data Content s
    = Data TyCon
    -- ^ Discrimination and projection axioms for a data type
    | Function Var
    -- ^ A definition of a function
    | Pointer Var
    -- ^ The pointer to a function definition or constructor
    | ExtensionalEquality
    -- ^ Extensional equality, (f @ x = g @ x) => f = g
    --   Toggled by a flag in HaloConf
    | Specific s
    -- ^ User specific content
  deriving (Eq,Ord)

instance Show s => Show (Content s) where
    show c = case c of
        Function v          -> "Function " ++ show v
        Pointer v           -> "Pointer " ++ show v
        Data tc             -> "Data " ++ showOutputable tc
        ExtensionalEquality -> "Extensional equality"
        Specific s          -> "Specific: " ++ show s

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
    { provides    :: Content s
    -- ^ Content defined
    , depends     :: [Content s]
    -- ^ Content depending upon
    , description :: String
    -- ^ Commentary
    , formulae    :: [Formula']
    -- ^ Formulae in this sub theory
    }

instance Show s => Show (Subtheory s) where
    show subthy = "Subtheory { content=" ++ show (provides subthy) ++ "}"

instance Eq s => Eq (Subtheory s) where
    (==) = (==) `on` provides

instance Ord s => Ord (Subtheory s) where
    compare = compare `on` provides

class Clausifiable s where
    mkClause :: s -> Formula' -> Clause'

instance Clausifiable s => Clausifiable (Content s) where
    mkClause (Specific s) = mkClause s
    mkClause Function{}   = clause A.Definition
    mkClause _            = clause A.Axiom

toClauses :: Clausifiable s => Subtheory s -> [Clause']
toClauses (Subtheory{..}) = commentary ++ map (mkClause provides) formulae
  where
    commentary
        | description /= "" = [comment description]
        | otherwise         = []
