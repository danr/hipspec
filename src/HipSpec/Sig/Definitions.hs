{-# LANGUAGE RecordWildCards #-}
module HipSpec.Sig.Definitions where

import Test.QuickSpec.Term (Symbol)
import qualified Test.QuickSpec.Term as QS
import qualified Test.QuickSpec.Equation as QS

import qualified HipSpec.Lang.Type as T

import HipSpec.Sig.Symbols
import HipSpec.Lang.PolyFOL
import HipSpec.Lang.ToPolyFOL
import HipSpec.Theory

import HipSpec.Id

import qualified HipSpec.Utils.PopMap as PM
import HipSpec.Utils.PopMap (PopMap)

import qualified Data.Map as M
import Data.Map (Map)

import Data.Maybe (catMaybes)
import Data.List (permutations)

type Id'      = Either Symbol LogicId

type VarMap   = PopMap (Type Id') Symbol

type ConMap = Map (Id,[Type Id']) Symbol

definitions :: Theory -> SymbolMap -> [QS.Equation]
definitions thy SymbolMap{..} = catMaybes
    [ trClause con_map var_map ts' cl
    | ((con,ts),_) <- M.toList con_map
    , Just cls <- [M.lookup con con_clauses]
    , cl <- cls
    , ts' <- permutations ts
    -- permutations in case quantifiers have become shuffled around
    ]
  where
    con_clauses :: Map Id [Clause Id']
    con_clauses = M.fromList
        [ (n,map (fmap Right) cls)
        | Subtheory (Definition n) cls _ <- thy
        ]

    var_mapping' :: Map Symbol (Type Id')
    var_mapping' = M.map k var_mapping
      where
        k :: (Id,T.Type Id) -> Type Id'
        k (_,t) = tr_type t

    tr_type :: T.Type Id -> Type Id'
    tr_type = fmap Right . trType

    var_map :: VarMap
    var_map = PM.reverseMap var_mapping'

    con_map :: ConMap
    con_map = M.fromList
        [ ((c,map tr_type ts),s)
        | (s,(c,_,ts)) <- M.toList con_mapping
        ]


trClause :: ConMap -> VarMap -> [Type Id'] -> Clause Id' -> Maybe QS.Equation
trClause cm pm tys cl = case cl of
    Clause _ Axiom tvs phi | equalLength tys tvs
        -> trFormula cm pm (fmInsts (zip tvs tys) phi)
    _   -> Nothing

trFormula :: ConMap -> VarMap -> Formula Id' -> Maybe QS.Equation
trFormula cm pm phi0 = case phi0 of
    Q Forall x t phi -> do
        case PM.pop t pm of
            Just (s,pm') -> trFormula cm pm' (fmSubst x (Var (Left s)) phi)
            _ -> Nothing
    TOp Equal lhs rhs -> do
        l <- trTerm cm lhs
        r <- trTerm cm rhs
        return (l QS.:=: r)
    _ -> Nothing

trTerm :: ConMap -> Term Id' -> Maybe QS.Term
trTerm cm = go
  where
    go tm0 = case tm0 of
        Var (Left s) -> return (QS.Var s)
        Apply (Right (Id f)) ts tms -> do
            tms' <- mapM go tms
            c <- M.lookup (f,ts) cm
            return (qsApp (QS.Const c) tms')
        Apply (Right App) [_,_] [t1,t2] -> do
            t1' <- go t1
            t2' <- go t2
            return (QS.App t1' t2')
        Apply (Right (Ptr f)) ts [] -> do
            c <- M.lookup (f,ts) cm
            return (QS.Const c)
        _ -> Nothing

qsApp :: QS.Term -> [QS.Term] -> QS.Term
qsApp = foldl QS.App

equalLength :: [a] -> [b] -> Bool
equalLength xs ys = k xs == k ys
  where k = map (const ())
