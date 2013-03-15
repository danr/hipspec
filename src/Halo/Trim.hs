{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables #-}
{-

   Trims away unnecessary function definitions from a grand theory.

   TODO: What about HipSpec's lemmas?

-}
module Halo.Trim where

import Halo.Subtheory

import Data.Maybe
import Data.Graph
import Data.Tree
import Data.List

-- | Trim down a grand theory, from the recursive dependencies from a set
--   of interesting subtheories.
--
--   We make a graph. Every recursive group defines some content fs
--   and depends on some content ds. Make an arrow from fs to each ds.
--   In the end, we follow all arrows from our initial important
--   subtheory.
--
--   We have keys as Content, and nodes are their corresponding Subtheories.
--
--   You can memo-thunk this function with the same grand_theory.
trim :: forall s . (Show s,Ord s) => [Subtheory s] -> [Content s] -> [Subtheory s]
trim grand_theory =
    let gr :: [(Subtheory s,Content s,[Content s])]
        gr = [ (subthy,provides subthy,depends subthy)
             | subthy <- grand_theory
             ]

        g          :: Graph
        fromVertex :: Vertex -> (Subtheory s,Content s,[Content s])
        toVertex   :: Content s -> Maybe Vertex
        (g,fromVertex,toVertex) = graphFromEdges gr

        err :: Content s -> Vertex
        err content = error $ "Halo.Trim.trim: Trying to find dependencies of "
                            ++ show content ++ " which could not be found!"

        findVertex :: Content s -> Vertex
        findVertex v = fromMaybe (err v) (toVertex v)

        get_subtheory :: (Subtheory s,Content s,[Content s]) -> Subtheory s
        get_subtheory (s,_,_) = s

    in  \ important ->
            let forest :: Forest Vertex
                forest = dfs g (map findVertex important)

            in  sort $ map (get_subtheory . fromVertex) (concatMap flatten forest)

