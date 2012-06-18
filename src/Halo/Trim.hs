{-

   Trims away unnecessary function definitions from the theory.

   TODO:

      * Do this for data types as well. Problem: need to find
        a good way to find all used data types in a function.

      * Do something similar for function pointers. For every function
        we decide to use, add its necessary function pointers.

-}
module Halo.Trim where

import Halo.Subtheory
import Halo.Util

import Var

import Data.Maybe
import Data.Graph
import Data.Tree

-- | Given a set of variables, removes all function definitions that
--   are not interesting.
--
--   We make a graph. Every recursive group defines some functions fs
--   and depends on some functions ds. Make an arrow from fs to each ds.
--   In the end, we follow all arrows from our initial variables.
--
--   We have keys as Var:s, and nodes are just dummy ().
--   Afterwards, we filter out those function definitions that do not
--   correspond to any interesting Var:s.
trim :: [Var] -> [Subtheory] -> [Subtheory]
trim vars subthys =
    let (g,fromVertex,toVertex) = graphFromEdges
            [ ((),v,fun_deps)
            | Subtheory (Function vs) all_deps _ _ <- subthys
            , let fun_deps = [ d | Function ds <- all_deps, d <- ds ]
            , v <- vs
            ]

        err :: Var -> Vertex
        err v = error $ "Halo.Trim.trim: Trying to find dependencies of the \
                        \variable " ++ show v ++ " which is not defined!"

        forest :: Forest Vertex
        forest = dfs g (map (\v -> fromMaybe (err v) (toVertex v)) vars)

        middle :: ((),Var,[Var]) -> Var
        middle (_,v,_) = v

        keep_vars :: [Var]
        keep_vars = map (middle . fromVertex) (concatMap flatten forest)

        keep :: Subtheory -> Bool
        keep (Subtheory (Function vs) _ _ _) = intersects keep_vars vs
        keep (Subtheory (Lemma _ vs) _ _ _)  = intersects keep_vars vs
        keep _                               = True

    in  filter keep subthys



