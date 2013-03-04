{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.Induction (induction) where

import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop
import HipSpec.Trans.Types
import HipSpec.Trans.TypeGuards
import HipSpec.Params

import Control.Concurrent.STM.Promise.Tree

import Halo.FOL.Abstract hiding (Term)
import Halo.Monad
import Halo.Util
import Halo.Shared
import Halo.Subtheory

import Data.Maybe (mapMaybe)

import Control.Monad.Reader
import Control.Monad.State

import qualified CoreSyn as C
import CoreSyn (CoreExpr)
import CoreSubst
import UniqSupply
import DataCon
import Type
import Var
import qualified Outputable as Outputable
import Induction.Structural hiding (Obligation)
import qualified Induction.Structural as IS

import HipSpec.Trans.MakerMonad
import HipSpec.Trans.Literal

induction :: forall eq . Params -> Property eq -> [Int] -> Maybe (MakerM (ProofTree eq))
induction Params{indhyps,indparts,bottoms} prop@Property{..} coords = do
    let obligs = subtermInduction (tyEnv bottoms) propVars coords
        n_obligs = length obligs

    -- If induction on these variables with this depth gives too many
    -- obligations, then do not do this induction, return Nothing
    guard (n_obligs <= indparts)

    -- Some parts give very many hypotheses. If this is the case,
    -- we cruelly drop some of the first weak ones
    let dropHyps oblig = oblig
            { hypotheses = take indhyps (reverse $ hypotheses oblig) }

    return $ fmap requireAll $ do

        -- Rename the variables
        obligs' <- fst <$> unTagMapM makeVar obligs

        forM (zip obligs' [0..]) $ \ (oblig,n) ->  do

            ((commentary,fs),ptrs) <- lift $ capturePtrs $ trObligation prop (dropHyps oblig)

            return $ Leaf $ Obligation
                { ob_prop = prop
                , ob_info = Induction
                    { ind_coords    = coords
                    , ind_num       = n
                    , ind_nums      = n_obligs
                    }
                , ob_content = Subtheory
                    { provides    = Specific Conjecture
                    , depends     = map Function propFunDeps ++ ptrs
                    , description = "Conjecture for " ++ propName ++ "\n" ++ commentary
                    , formulae    = fs
                    }
                }

data Loc = Hyp | Concl

makeVar :: Tagged Var -> MakerM Var
makeVar (v :~ _) = do
    (u,us) <- takeUniqFromSupply <$> get
    put us
    return (setVarUnique v u)

trObligation :: Property eq -> IS.Obligation DataCon Var Type
             -> HaloM (String,[Formula'])
trObligation Property{..} obligation@(IS.Obligation skolems hyps concl) =

    local (addSkolems skolem_vars) $ do

        tr_hyps <- mapM trHyp hyps

        tr_concl <- splitFormula <$> trPred Concl concl

        return
            ("Proof by structural induction\n" ++
                render (linObligation ghcStyle obligation)
            ,tr_concl ++ tr_hyps ++ mapMaybe typeGuardSkolem skolem_vars
            )

  where

    skolem_vars = map fst skolems

    trPred :: Loc -> [Term DataCon Var] -> HaloM Formula'
    trPred loc tms = do
        (tr_lit,lit_mins) <- trLiteral propLiteral'
        (assums,_) <- mapAndUnzipM trLiteral propAssume'
        return $ case loc of
                Hyp   -> ors (map min' lit_mins) ==> (assums ===> tr_lit)
                Concl -> ands $ map minrec lit_mins ++ [neg tr_lit] ++ assums
      where
        s = extendIdSubstList emptySubst
                [ (v,trTerm t) | (v,_) <- propVars | t <- tms ]

        propLiteral':propAssume' = flip map (propLiteral:propAssume) $ \ eq ->
            case eq of
                e1 :== e2 -> substExpr (Outputable.text "trPred") s e1 :==
                             substExpr (Outputable.text "trPred") s e2
                Total e   -> Total (substExpr (Outputable.text "trPred") s e)

    trHyp :: Hypothesis DataCon Var Type -> HaloM Formula'
    trHyp (_,tms) = foralls <$> trPred Hyp tms

trTerm :: Term DataCon Var -> CoreExpr
trTerm (Var x)    = C.Var x
trTerm (Con c as) = foldl C.App (C.Var (dataConWorkId c)) (map trTerm as)
trTerm (Fun f as) = foldl C.App (C.Var f) (map trTerm as)

ghcStyle :: Style DataCon Var Type
ghcStyle = Style
    { linc = text . showOutputable
    , linv = text . showOutputable
    , lint = text . showOutputable
    }


