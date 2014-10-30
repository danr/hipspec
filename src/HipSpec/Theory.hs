{-# LANGUAGE ViewPatterns,RecordWildCards,PatternGuards,ScopedTypeVariables #-}
module HipSpec.Theory
    ( module HipSpec.Pretty
    , ArityMap
    , combineArityMap
    , emptyArityMap
    , primOpArities
    , Content(..)
    , Theory
    , Subtheory(..)
    , dependencies
    , subtheory
    , calcDeps
    , calcDepsIgnoring
    , sortClauses
    ) where

import HipSpec.Pretty

import HipSpec.Id

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.ToPolyFOL (Poly(..))

-- import Name

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.List (sortBy)
import Data.Ord (comparing)

import PrimOp

type ArityMap = Map Id Int

combineArityMap :: ArityMap -> ArityMap -> ArityMap
combineArityMap = M.union

emptyArityMap :: ArityMap
emptyArityMap = M.empty

primOpArities :: ArityMap
primOpArities = M.fromList
    [ (idFromPrimOp op,arity)
    | op <- allThePrimOps, let (_,_,_,arity,_) = primOpSig op
    ]

data Content
    = Definition Id
    -- ^ Function definition, or a constructor,
    --   with no clauses and only depends on its parent data type
    | Type Id
    -- ^ Axioms for a type
    | Pointer Id
    -- ^ Pointer to some defined name
    | Lemma Int
    -- ^ A lemma
    | Conjecture
    -- ^ The conjecture
    | AppThy
    -- ^ Defines app and fn
  deriving (Eq,Ord)

instance Show Content where
    show ctnt = case ctnt of
        Definition rn -> "Definition " ++ ppId rn
        Type nm       -> "Type " ++ ppId nm
        Pointer rn    -> "Pointer " ++ ppId rn
        Lemma i       -> "Lemma " ++ show i
        Conjecture    -> "Conjecture"
        AppThy        -> "AppThy"

type Theory = [Subtheory]

data Subtheory = Subtheory
    { defines :: Content
    , clauses :: [Clause LogicId LogicId]
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
    { deps = S.unions [types,app,ptrs,defs] S.\\ S.fromList ctnt }
  where
    (S.toList -> ty_cons,S.toList -> fns) = clsDeps (clauses s)

    types = S.fromList [ Type x | Id x@GHCOrigin{} <- ty_cons ]

    app = S.fromList $ [ AppThy | TyFn <- ty_cons ] ++ [ AppThy | App <- fns ]

    ptrs = S.fromList [ Pointer x | Ptr x <- fns ]

    defs = S.fromList . map Definition $
        [ x | Id x <- fns ] ++ [ x | Proj x _ <- fns ]

-- | Sort clauses: first sort signatures, then type signatures, then axioms and
--   at last the goal.
sortClauses :: forall a b . Bool -> [Clause a b] -> [Clause a b]
sortClauses push_data_types = sortBy (comparing rank)
  where
    rank :: Clause a b -> Int
    rank SortSig{}                                 = 0
    rank TypeSig{}                                 = 2
    rank cl@Clause{} | DataDecl{} <- cl_formula cl = if push_data_types then 1 else 3
    rank cl@Clause{} | Goal <- cl_type cl          = 4
    rank Clause{}                                  = 3
    rank Comment{}                                 = 3

