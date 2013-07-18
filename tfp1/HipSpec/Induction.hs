{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Induction (induction) where

-- TODO: Structural induction
-- Remember that Rename can be used as local skolems

import HipSpec.ThmLib
import HipSpec.Theory
import HipSpec.Translate
import HipSpec.Property
import HipSpec.Literal

import Lang.RichToSimple (Loc(..),Rename(..))
import qualified Lang.Simple as S
import Lang.Simple (Type,Typed(..))

import Lang.PolyFOL hiding (Type(..),Term(..))
import qualified Lang.PolyFOL as P
import Lang.ToPolyFOL

import Induction.Structural hiding (Obligation)
import qualified Induction.Structural as IS

import Control.Monad
import Data.Maybe (isJust)

indhyps :: Int
indhyps   = 500

indobligs :: Int
indobligs = 20

induction :: TyEnv' -> ArityMap -> Property eq -> [Int] -> Maybe [ProofObligation eq]
induction ty_env am (tvSkolemProp -> (prop@Property{..},sorts,ignore)) coords = do
    -- Applying structural induction
    let vars     = [ (v,t) | v ::: t <- prop_vars ]
        obligs   = subtermInduction ty_env vars coords
        n_obligs = length obligs

    -- If induction on these variables with this depth gives too many
    -- obligations, then do not do this induction, return Nothing
    guard (n_obligs <= indobligs)
    guard $ all isJust
        [ ty_env t | c <- coords, let (_,t) = vars !! c ]

    -- Some parts give very many hypotheses. If this is the case,
    -- we cruelly drop some of the first weak ones
    let dropHyps oblig = oblig
            { hypotheses = take indhyps (reverse $ hypotheses oblig) }

    -- Localise all names
    let obligs' :: [IS.Obligation Con Name' (Type Name')]
        obligs' = unTag (\ (v :~ i) -> New [LetLoc v] i) obligs

    return
        [ Obligation
            { ob_prop = prop
            , ob_info = Induction
                { ind_coords    = coords
                , ind_num       = n
                , ind_nums      = n_obligs
                }
            , ob_content = calcDepsIgnoring ignore subtheory
                { defines = Conjecture
                , clauses = sorts ++ cls
                }
            }
        | (oblig,n) <- zip obligs' [0..]
        , let cls = tr_oblig (dropHyps oblig)
        ]
  where
    tr_oblig :: IS.Obligation Con Name' (Type Name') -> [Clause LogicId]
    tr_oblig (IS.Obligation skolems hyps concl) =

        -- Type signatures for skolemised variables
        [ TypeSig i [] [] t | (i,t) <- tr_quant skolems ]
        ++

        -- Hypotheses
        [ Clause Nothing Axiom []
            $ forAlls (tr_quant qs) (tr_pred (skolems ++ qs) p)
        | (qs,p) <- hyps
        ]
        ++

        -- Goal
        [ Clause Nothing Goal [] (tr_pred skolems concl) ]

    tr_quant :: [(Name',Type Name')] -> [(LogicId,P.Type LogicId)]
    tr_quant qs = [ (Id x,trType t) | (x,t) <- qs ]

    tr_pred :: [(Name',Type Name')] -> [Term Con Name'] -> Formula LogicId
    tr_pred scope tms = tr_assums ===> tr_goal
      where
        -- Scope for trLiteral
        sc = map fst scope

        -- Lookup for trTerm
        lkup :: Name' -> Typed Name'
        lkup x = case lookup x scope of
            Just t  -> x ::: t
            Nothing -> error $ "HipSpec.Induction: Variable " ++ ppRename x ++ " lost!"

        -- Translated goals to assumptions
        tr_goal:tr_assums = map (trLiteral am sc) (goal:assums)

        -- Goals and assumptions where the property variables are replaced with
        -- the induction predicate's
        goal:assums = map subst (prop_goal:prop_assums)

        -- | substitute the prop vars
        subst :: Literal -> Literal
        subst = mapLiteral $ S.substMany
            [ (v,trTerm lkup t) | v <- prop_vars | t <- tms ]

trTerm :: (Name' -> Typed Name') -> Term Con Name' -> S.Expr (Typed Name')
trTerm lkup = go
  where
    go :: Term Con Name' -> S.Expr (Typed Name')
    go tm = case tm of
        IS.Var x          -> S.Var (lkup x) []
        IS.Con (c,ts) tms -> S.apply (S.Var c (map S.star ts)) (map go tms)
        IS.Fun f      tms -> S.apply (S.Var (lkup f) []) (map go tms)

