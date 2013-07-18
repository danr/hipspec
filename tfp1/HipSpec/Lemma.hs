-- | Translate a property as a lemma
{-# LANGUAGE RecordWildCards #-}
module HipSpec.Lemma where

import HipSpec.Theory as T
import HipSpec.Literal
import HipSpec.Property

import Lang.PolyFOL as P
import Lang.ToPolyFOL
import Lang.Simple

trLemma :: ArityMap -> Int -> Property eq -> Subtheory
trLemma am i Property{..} = calcDeps subtheory
    { defines = Lemma i
    , clauses = [clause]
    }
  where
    scope       = map forget_type prop_vars

    goal:assums = map (trLiteral am scope) (prop_goal:prop_assums)

    quants      = [ (Id x,trType t) | x ::: t <- prop_vars ]

    clause       = Clause (Just i) Axiom (map Id prop_tvs)
                 $ forAlls quants (assums ===> goal)

