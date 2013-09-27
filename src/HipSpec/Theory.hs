{-# LANGUAGE ViewPatterns,RecordWildCards,PatternGuards,ScopedTypeVariables #-}
module HipSpec.Theory
    ( module HipSpec.Pretty
    , ArityMap
    , initArityMap
    , combineArityMap
    , Content(..)
    , Theory
    , Subtheory(..)
    , dependencies
    , subtheory
    , calcDeps
    , calcDepsIgnoring
    , sortClauses
    , bottomThy
    ) where

import HipSpec.Pretty

import HipSpec.Lang.RichToSimple (Rename(..))
import HipSpec.Lang.PolyFOL
import HipSpec.Lang.ToPolyFOL (Poly(..))

import Name

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.List (sortBy)
import Data.Ord (comparing)

type ArityMap = Map (Rename Name) Int

combineArityMap :: ArityMap -> ArityMap -> ArityMap
combineArityMap = M.union

initArityMap :: ArityMap
initArityMap = M.singleton Bottom 0

data Content
    = Definition (Rename Name)
    -- ^ Function definition, or a constructor,
    --   with no clauses and only depends on its parent data type
    | Type Name
    -- ^ Axioms for a type
    | Pointer (Rename Name)
    -- ^ Pointer to some defined name
    | Lemma Int
    -- ^ A lemma
    | Conjecture
    -- ^ The conjecture
    | AppThy
    -- ^ Defines app and fn
    | BottomThy
    -- ^ Defines the type of bottom
  deriving (Eq,Ord)

instance Show Content where
    show ctnt = case ctnt of
        Definition rn -> "Definition " ++ ppRename rn
        Type nm       -> "Type " ++ ppName nm
        Pointer rn    -> "Pointer " ++ ppRename rn
        Lemma i       -> "Lemma " ++ show i
        Conjecture    -> "Conjecture"
        AppThy        -> "AppThy"
        BottomThy     -> "BottomThy"

type Theory = [Subtheory]

data Subtheory = Subtheory
    { defines :: Content
    , clauses :: [Clause LogicId]
    , deps    :: Set Content
    }

dependencies :: Subtheory -> [Content]
dependencies = S.toList . deps

instance Show Subtheory where
    show Subtheory{..} = concatMap (++ "\n    ")
        [ "Subtheory"
        , "{ defines = " ++ show defines
        , ", clauses = " ++ ppAltErgo clauses
        , ", deps = " ++ show (S.toList deps)
        , "}"
        ]

-- | A dummy subtheory to initialise without dependencies
subtheory :: Subtheory
subtheory = Subtheory err err err
  where
    err = error "subtheory uninitialised field"

-- | Calculates and sets the dependencies for a subtheory
calcDeps :: Subtheory -> Subtheory
calcDeps = calcDepsIgnoring []

-- | Calculate depedencies, ignoring some content
calcDepsIgnoring :: [Content] -> Subtheory -> Subtheory
calcDepsIgnoring ctnt s = s
    { deps = add_bot (S.unions [types,app,ptrs,defs] S.\\ S.fromList ctnt) }
  where
    (S.toList -> ty_cons,S.toList -> fns) = clsDeps (clauses s)

    types = S.fromList [ Type x | Id (Old x) <- ty_cons ]

    app = S.fromList $ [ AppThy | TyFn <- ty_cons ] ++ [ AppThy | App <- fns ]

    ptrs = S.fromList [ Pointer x | Ptr x <- fns ]

    defs = S.fromList . map Definition $
        [ x | Id x <- fns, x /= Bottom ] ++ [ x | Proj x _ <- fns ]

    add_bot
        | and [ True | Id Bottom <- fns ] = S.insert BottomThy
        | otherwise                       = id

-- | Sort clauses: first sort signatures, then type signatures, then axioms and
--   at last the goal.
sortClauses :: forall a . [Clause a] -> [Clause a]
sortClauses = sortBy (comparing rank)
  where
    rank :: Clause a -> Int
    rank SortSig{}                        = 0
    rank TypeSig{}                        = 1
    rank cl@Clause{} | Goal <- cl_type cl = 3
    rank _                                = 2


bottomThy :: Subtheory
bottomThy = Subtheory
    { defines = BottomThy
    , clauses = [TypeSig (Id Bottom) [QVar 0] [] (TyVar (QVar 0))]
    , deps    = S.empty
    }

