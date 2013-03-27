{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables #-}
-- Sort functions according to the call graph
module HipSpec.Heuristics.CallGraph where

import Test.QuickSpec.Term

import HipSpec.Heuristics.Calls
import HipSpec.GHC.SigMap

import Halo.Shared (isDataConId)
import Halo.Util

import Data.Map (Map)
import qualified Data.Map as M

import Id

import Data.Maybe
import Data.Graph hiding (edges)

sortByCallGraph :: SigMap -> (a -> [Symbol]) -> [a] -> [[a]]
sortByCallGraph = sortByGraph . transitiveCallGraph

sortByGraph :: forall a s . Ord s => Map s [s] -> (a -> [s]) -> [a] -> [[a]]
sortByGraph cg syms eqs = flattenSCCs sccs
  where
    cglkup :: a -> [s]
    cglkup = nubSorted . concat . mapMaybe (`M.lookup` cg) . syms

    ann :: [([s],a)]
    ann = map (cglkup &&& id) eqs

    grouped :: [[([s],a)]]
    grouped = groupSortedOn fst ann

    eqcs :: [([s],[a])]
    eqcs = map ((fst . head) &&& map snd) grouped

    sss :: [[s]]
    sss = map fst eqcs

    graph :: [([a],[s],[[s]])]
    graph = [ (eqc,ss,filter (ss `isSupersetOf`) sss)
            | (ss,eqc) <- eqcs
            ]

    sccs :: [SCC [a]]
    sccs = stronglyConnComp graph

isSupersetOf :: Eq a => [a] -> [a] -> Bool
as `isSupersetOf` bs = all (`elem` as) bs

-- | Calculate the call graph for the QuickSpec string marshallings
transitiveCallGraph :: SigMap -> Map Symbol [Symbol]
transitiveCallGraph (SigMap si _) = M.fromList
    [ (s,mapMaybe (`M.lookup` ism) (varSetElems (transCalls Without i)))
    | (i,s) <- is
    ]
  where
    is :: [(Id,Symbol)]
    is = [ (i,s) | (s,i) <- M.toList si, not (isDataConId i) ]

    ism :: Map Id Symbol
    ism = M.fromList is

