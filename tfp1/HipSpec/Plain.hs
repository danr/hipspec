-- | Plain, definitional equality
{-# LANGUAGE RecordWildCards,ViewPatterns #-}
module HipSpec.Plain where

import HipSpec.Theory as T
import HipSpec.Literal
import HipSpec.Property
import HipSpec.ThmLib

import Lang.PolyFOL as P
import Lang.ToPolyFOL
import Lang.Simple

plain :: ArityMap -> Property -> ProofObligation
plain am prop_orig@(tvSkolemProp -> (Property{..},sorts,ignore)) = Obligation
    { ob_prop = prop_orig
    , ob_info = Induction [] 0 1
    , ob_content = calcDepsIgnoring ignore subtheory
        { defines = T.Conjecture
        , clauses = goal_cl : sorts
        }
    }
  where
    scope       = map forget_type prop_vars

    goal:assums = map (trLiteral am scope) (prop_goal:prop_assums)

    quants      = [ (Id x,trType t) | x ::: t <- prop_vars ]

    goal_cl = Clause Nothing Goal (map Id prop_tvs)
            $ forAlls quants (assums ===> goal)

