{-# LANGUAGE RecordWildCards #-}
module Halo.Subtheory where

import Halo.Util
import Halo.Shared
import Halo.FOL.Abstract hiding (Lemma)
import qualified Halo.FOL.Abstract as A

import Var
import TyCon

import Data.Function

data Content
    = ExtensionalEquality
    -- ^ Extensional equality, (f @ x = g @ x) => f = g, has a flag in HaloConf
    | PrimConAxioms
    -- ^ [contracts only] Axioms about UNR and BAD
    | PrimConApps
    -- ^ [contracts only] App on UNR and BAD
    | Data TyCon
    -- ^ Discrimination and projection axioms for a data type
    | CrashFree TyCon
    -- ^ [contracts only] CF predicates for a data type
    | Typing TyCon
    -- ^ [hipspec only] Type predicates for a data type
    | Function Var
    -- ^ A definition of a function
    | Pointer Var
    -- ^ The pointer to a function definition or constructor
    | Lemma String [Var]
    -- ^ [hipspec only] Lemma with a name, regarding a group of definitions
  deriving (Eq,Ord)

instance Show Content where
    show c = case c of
        Function v    -> "Function " ++ show v
        Pointer v     -> "Pointer " ++ show v
        Data tc       -> "Data " ++ showOutputable tc
        CrashFree tc  -> "CrashFree " ++ showOutputable tc
        PrimConAxioms -> "PrimConAxioms"
        Typing tc     -> "Typing " ++ showOutputable tc
        Lemma s vs    -> "Lemma " ++ s ++ " (" ++ unwords (map show vs) ++ ")"

-- | A subtheory
--
--   Provides some content, and can also depend upon other content.
--
--   The provides fields should be unique when assembling a grand theory,
--   Eq and Ord instances are on this field.
--
--   There is an optional description which is translated to a TPTP
--   comment for debug output.
data Subtheory = Subtheory
    { provides    :: Content
    -- ^ Content defined
    , depends     :: [Content]
    -- ^ Content depending upon
    , description :: String
    -- ^ Commentary
    , formulae    :: [Formula']
    -- ^ Formulae in this sub theory
    }

instance Show Subtheory where
  show subthy = "Subtheory { content=" ++ show (provides subthy) ++ "}"

instance Eq Subtheory where
  (==) = (==) `on` provides

instance Ord Subtheory where
  compare = compare `on` provides

toClauses :: Subtheory -> [Clause']
toClauses (Subtheory{..}) =
    (description /= "" ? (comment description:))
    (map (namedClause name cltype) formulae)
  where
    name   = case provides of
                 Lemma s _ -> "Lemma{" ++ s ++ "}"
                 _         -> "x"

    cltype = case provides of
                 Lemma{}    -> A.Lemma
                 Function{} -> A.Definition
                 _          -> A.Axiom
