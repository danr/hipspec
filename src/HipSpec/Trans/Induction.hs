{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.Induction (induction) where

import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop
import HipSpec.Trans.Types
import HipSpec.Params

import Control.Concurrent.STM.Promise.Tree

import Halo.FOL.Abstract hiding (Term)
import Halo.Monad
import Halo.Util
import Halo.Shared
import Halo.MonoType

import Control.Monad.Reader

import MkCore (mkImpossibleExpr)
import qualified CoreSyn as C
import CoreSyn (CoreExpr)
import CoreSubst
import DataCon
import Type
import Var
import qualified Outputable as Outputable
import Induction.Structural hiding (Obligation)
import qualified Induction.Structural as IS

import HipSpec.Trans.MakerMonad
import HipSpec.Trans.Literal

induction :: forall eq . Params -> Property eq -> [Int] -> Maybe (MakerM (ProofTree eq))
induction Params{indhyps,indobligs,bottoms} prop@Property{..} coords = do
    let obligs = subtermInduction (tyEnv bottoms) propVars coords
        n_obligs = length obligs

    -- If induction on these variables with this depth gives too many
    -- obligations, then do not do this induction, return Nothing
    guard (n_obligs <= indobligs)

    -- Some parts give very many hypotheses. If this is the case,
    -- we cruelly drop some of the first weak ones
    let dropHyps oblig = oblig
            { hypotheses = take indhyps (reverse $ hypotheses oblig) }

    return $ fmap requireAll $ do

        -- Rename the variables
        obligs' <- fst <$> unTagMapM makeVar obligs

        forM (zip obligs' [0..]) $ \ (oblig,n) ->  do

            cls <- lift $ trObligation prop (dropHyps oblig)

            return $ Leaf $ Obligation
                { ob_prop = prop
                , ob_info = Induction
                    { ind_coords    = coords
                    , ind_num       = n
                    , ind_nums      = n_obligs
                    }
                , ob_content = calculateDeps subtheory
                    { provides = Specific Conjecture
                    , depends  = propDeps
                    , clauses  = comment ("Conjecture for " ++ propName) : cls
                    }
                }

data Loc = Hyp | Concl

makeVar :: Tagged Var -> MakerM Var
makeVar (v :~ _) = do
    u <- makeUnique
    return (setVarUnique v u)

trObligation :: Property eq -> IS.Obligation (Either DataCon Bottom) Var Type
             -> HaloM [Clause']
trObligation Property{..} obligation@(IS.Obligation skolems hyps concl) = do

    sks <- sequence [ (,) s <$> monoType t | (s,t) <- skolems ]

    local (addSkolems sks) $ do

        tr_hyps <- mapM trHyp hyps

        tr_concl <- splitFormula <$> trPred Concl concl

        return $
            comment "Proof by structural induction" :
            comment (render (linObligation ghcStyle obligation)) :
            map (uncurry (typeSig' . ASkolem)) sks ++
            map negatedConjecture tr_concl ++
            map hypothesis tr_hyps

  where

    trPred :: Loc -> [Term (Either DataCon Bottom) Var] -> HaloM Formula'
    trPred loc tms = do
        tr_lit <- trLiteral propLiteral'
        assums <- mapM trLiteral propAssume'
        return $ case loc of
            Hyp   -> assums ===> tr_lit
            Concl -> ands (neg tr_lit:assums)
      where
        s = extendIdSubstList emptySubst
                [ (v,trTerm t) | (v,_) <- propVars | t <- tms ]

        propLiteral':propAssume' = flip map (propLiteral:propAssume) $ \ eq ->
            case eq of
                e1 :== e2 -> substExpr (Outputable.text "trPred") s e1 :==
                             substExpr (Outputable.text "trPred") s e2
                Total t e -> Total t (substExpr (Outputable.text "trPred") s e)

    trHyp :: Hypothesis (Either DataCon Bottom) Var Type -> HaloM Formula'
    trHyp (qvs,tms) = local
        (addQuantVars [ setVarType q t | (q,t) <- qvs ]) $
        foralls varMonoType =<< trPred Hyp tms

trTerm :: Term (Either DataCon Bottom) Var -> CoreExpr
trTerm (Var x)           = C.Var x
trTerm (Con (Right (Bottom ty)) []) = mkImpossibleExpr ty
trTerm (Con (Right (Bottom _)) _)   = error "Internal error: Induction on bottom applied to arguments"
trTerm (Con (Left c) as) = foldl C.App (C.Var (dataConWorkId c)) (map trTerm as)
trTerm (Fun f as)        = foldl C.App (C.Var f) (map trTerm as)

ghcStyle :: Style (Either DataCon Bottom) Var Type
ghcStyle = Style
    { linc = \ c -> case c of
                Right (Bottom ty) -> text $ "bottom@" ++ showOutputable ty
                Left dc           -> text (showOutputable dc)
    , linv = text . showOutputable
    , lint = text . showOutputable
    }


