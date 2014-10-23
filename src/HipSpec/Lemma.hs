-- | Translate a property as a lemma
{-# LANGUAGE RecordWildCards #-}
module HipSpec.Lemma where

import HipSpec.Theory as T
import HipSpec.Literal
import HipSpec.Property

import HipSpec.Lang.PolyFOL as P
import HipSpec.Lang.ToPolyFOL
-- import HipSpec.Lang.Simple

trLemma :: ArityMap -> Int -> Property -> Subtheory
trLemma am i Property{..} = calcDeps subtheory
    { defines = Lemma i
    , clauses = [clause]
    }
  where
    scope       = map fst prop_vars

    goal:assums = map (trLiteral am scope) (prop_goal:prop_assums)

    quants      = [ (Id x,trType t) | (x,t) <- prop_vars ]

    clause       = Clause (Just i) [] Axiom (map Id prop_tvs)
                 $ forAlls quants (assums ===> goal) `withQID` mkQID prop_name

mkQID :: String -> QID
mkQID s = "|{" ++ filter (/= '|') s ++ "}|"

