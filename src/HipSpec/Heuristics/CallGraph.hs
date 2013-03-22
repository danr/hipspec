{-# LANGUAGE NamedFieldPuns #-}
-- Sort functions according to the call graph
module HipSpec.Heuristics.CallGraph where

import Test.QuickSpec.Term

import HipSpec.StringMarshal

import Halo.Shared (isDataConId)

import Data.Map (Map)
import qualified Data.Map as M

import CoreSyn
import Id
import VarSet
import CoreFVs

import Data.Maybe

import Data.Graph

sortByCallGraph :: StrMarsh -> (a -> [Symbol]) -> [a] -> [[a]]
sortByCallGraph = sortByGraph . transitiveCallGraph

sortByGraph :: Ord s => Map s [s] -> (a -> [s]) -> [a] -> [[a]]
sortByGraph m k = stronglyConnComp . map u
  where u a = let s = k a in (a,s,POWERSET fromMaybe [] (M.lookup s m)
                                -- ^ TODO: k a : [s], so make this point to all subsets
                                --

-- | Calculate the call graph for the QuickSpec string marshallings
transitiveCallGraph :: StrMarsh -> Map Symbol [Symbol]
transitiveCallGraph (si,_) = M.fromList
    [ (s,mapMaybe (`M.lookup` ism) (varSetElems (calls' i)))
    | (i,s) <- is
    ]

  where
    is :: [(Id,Symbol)]
    is = [ (i,s) | (s,i) <- M.toList si, not (isDataConId i) ]

    ism :: Map Id Symbol
    ism = M.fromList is

    -- | The functions this function calls transitively
    calls' :: Id -> VarSet
    calls' v = go emptyVarSet (unitVarSet v)
      where
        go visited queue
            | isEmptyVarSet to_visit = visited
            | otherwise = go (visited `unionVarSet` to_visit)
                             (foldVarSet (\ i vs -> calls i `unionVarSet` vs)
                                         emptyVarSet
                                         to_visit)
          where to_visit = queue `minusVarSet` visited

-- | The functions this functions calls (not transitively)
calls :: Id -> VarSet
calls v = case realIdUnfolding v of
    CoreUnfolding{uf_tmpl} ->
        let k v' = (isLocalId v' || isGlobalId v') && not (isDataConId v')
        in  exprSomeFreeVars k uf_tmpl
    _ -> emptyVarSet

