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
import HipSpec.Params

import qualified HipSpec.Lang.Simple as S
import HipSpec.Lang.Simple (Type)

import HipSpec.Lang.PolyFOL hiding (Type(..),Term(..))
import qualified HipSpec.Lang.PolyFOL as P
import HipSpec.Lang.ToPolyFOL

import HipSpec.Id

import Induction.Structural hiding (Obligation)
import qualified Induction.Structural as IS

import Control.Monad
import Data.Maybe (isJust)

induction :: Params -> TyEnv' -> ArityMap -> Property eq -> [Int] -> Maybe [ProofObligation eq]
induction Params{indhyps,indobligs} ty_env am (tvSkolemProp -> (prop@Property{..},sorts,ignore)) coords = do
    -- Applying structural induction
    let obligs   = subtermInduction ty_env prop_vars coords
        n_obligs = length obligs

    -- If induction on these variables with this depth gives too many
    -- obligations, then do not do this induction, return Nothing
    guard (n_obligs <= indobligs)
    guard $ all isJust
        [ ty_env t | c <- coords, let (_,t) = prop_vars !! c ]

    -- Some parts give very many hypotheses. If this is the case,
    -- we cruelly drop some of the first weak ones
    let dropHyps oblig = oblig
            { hypotheses = take indhyps (reverse $ hypotheses oblig) }

    -- Localise all names
    let obligs' :: [IS.Obligation Con Id (Type Id)]
        obligs' = unTag (\ (v :~ i) -> mkLetFrom v i prop_id) obligs

    return
        [ Obligation
            { ob_prop = prop
            , ob_info = ObInduction
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
    tr_oblig :: IS.Obligation Con Id (Type Id) -> [Clause LogicId LogicId]
    tr_oblig (IS.Obligation skolems hyps concl) =

        -- Type signatures for skolemised variables
        [ TypeSig i [] [] t | (i,t) <- tr_quant skolems ]
        ++

        -- Hypotheses
        [ Clause Nothing [Source] Axiom []
            $ forAlls (tr_quant qs) (tr_pred skolems qs p)
        | (qs,p) <- hyps
        ]
        ++

        -- Goal
        [ Clause Nothing [Source] Goal [] (tr_pred skolems [] concl) ]

    tr_quant :: [(Id,Type Id)] -> [(LogicId,P.Type LogicId LogicId)]
    tr_quant qs = [ (Id x,trType t) | (x,t) <- qs ]

    tr_pred :: [(Id,Type Id)] -> [(Id,Type Id)] -> [Term Con Id] -> Formula LogicId LogicId
    tr_pred skolems scope tms = tr_assums ===> tr_goal
      where
        -- Scope for trLiteral
        sc = map fst scope

        -- Lookup for trTerm
        lkup :: Id -> (Id,Type Id)
        lkup x = case lookup x (skolems ++ scope) of
            Just t  -> (x,t)
            Nothing -> error $ "HipSpec.Induction: Variable " ++ ppId x ++ " lost!"

        -- Translated goals to assumptions
        tr_goal:tr_assums = map (trLiteral am sc) (goal:assums)

        -- Goals and assumptions where the property variables are replaced with
        -- the induction predicate's
        goal:assums = map subst (prop_goal:prop_assums)

        -- | substitute the prop vars
        subst :: Literal -> Literal
        subst = mapLiteral $ S.substMany
            [ (v,trTerm lkup t) | (v,_) <- prop_vars | t <- tms ]

trTerm :: (Id -> (Id,Type Id)) -> Term Con Id -> S.Expr Id
trTerm lkup = go
  where
    go :: Term Con Id -> S.Expr Id
    go tm = case tm of
        IS.Var x            -> uncurry S.Lcl (lkup x)
        IS.Con (c,t,ts) tms -> S.apply (S.Gbl c t ts) (map go tms)
        IS.Fun f        tms -> S.apply (uncurry S.Lcl (lkup f)) (map go tms)
                                    {- locally quantified functions -}

