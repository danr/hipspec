{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables #-}
{-

   Trims away unnecessary function definitions from the theory.

   TODO: What about HipSpec's lemmas?

-}
module Halo.Trim where

import Halo.Subtheory
import Halo.Util
import Halo.Conf

import Var

import Data.Maybe
import Data.Graph
import Data.Tree
import Data.List

-- | Given a set of variables corresponding to top level definitions,
--   removes all function definitions that are not interesting.
trimFuns :: (Ord s,Show s) => HaloConf -> [Var] -> [Subtheory s] -> [Subtheory s]
trimFuns HaloConf{use_cf} vars grand_theory = trim important grand_theory
  where important =
            [ Function v
            | Subtheory (Function v) _ _ _ <- grand_theory
            , v `elem` vars
            ]

-- | Trim down a grand theory, from the recursive dependencies from a set
--   of interesting subtheories.
--
--   We make a graph. Every recursive group defines some content fs
--   and depends on some content ds. Make an arrow from fs to each ds.
--   In the end, we follow all arrows from our initial important
--   subtheory.
--
--   We have keys as Content, and nodes are their corresponding Subtheories.
trim :: forall s . (Show s,Ord s) => [Content s] -> [Subtheory s] -> [Subtheory s]
trim important grand_theory =
    let gr :: [(Subtheory s,Content s,[Content s])]
        gr = [ (subthy,provides subthy,depends subthy)
             | subthy <- grand_theory
             ]

        g          :: Graph
        fromVertex :: Vertex -> (Subtheory s,Content s,[Content s])
        toVertex   :: Content s -> Maybe Vertex
        (g,fromVertex,toVertex) = graphFromEdges gr

        err :: Content s -> Vertex
        err subthy = error $ "Halo.Trim.trim: Trying to find dependencies of "
                            ++ show subthy ++ " which could not be found!"

        forest :: Forest Vertex
        forest = dfs g (map (\v -> fromMaybe (err v) (toVertex v)) important)

        subtheory :: (Subtheory s,Content s,[Content s]) -> Subtheory s
        subtheory (s,_,_) = s

    in  sort $ map (subtheory . fromVertex) (concatMap flatten forest)
