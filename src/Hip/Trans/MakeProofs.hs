{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns #-}
module Hip.Trans.MakeProofs where

import Hip.Induction
import Hip.Induction.Linearise
import Hip.Trans.ProofDatatypes
import Hip.Trans.Theory as Thy
import Hip.Trans.Types
import Hip.Params

import Halo.FOL.Abstract hiding (Term,Lemma)
import Halo.ExprTrans
import Halo.Monad
import Halo.Util
import Halo.Shared
import Halo.Subtheory

import qualified Data.Map as M
import Data.Map (Map)
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
import Id
import Outputable hiding (equals)

import qualified Text.PrettyPrint as P

type MakerM = StateT (UniqSupply,Map (Var,Integer) Var) HaloM

getVar :: Var -> Integer -> MakerM Var
getVar v i = do
    m_v <- gets (M.lookup (v,i) . snd)
    case m_v of
        Just v' -> return v'
        Nothing -> do
            (u,us) <- takeUniqFromSupply <$> gets fst
            let v' = setVarUnique v u
            modify (const us *** M.insert (v,i) v')
            return v'

runMakerM :: HaloEnv -> UniqSupply -> MakerM a -> ((a,[String]),UniqSupply)
runMakerM env us mm =
    let ((hm,(us',_)),msg) = runHaloM env (runStateT mm (us,M.empty))
    in  ((hm,msg),us')

trLemma :: Prop -> HaloM Subtheory
trLemma lemma@Prop{..} = do
    (tr_lem,ptrs) <- capturePtrs equals
    return $ Subtheory
        { provides    = Lemma propRepr propFunDeps
        , depends     = map Function propFunDeps ++ map Pointer ptrs
        , description = "Lemma " ++ propRepr
                        ++ "\ndependencies: " ++ unwords (map idToStr propFunDeps)
        , formulae    = tr_lem
        }
  where
    vars = map fst propVars

    equals :: HaloM [Formula']
    equals = local (pushQuant vars) $ do
        lhs <- trExpr proplhs
        rhs <- trExpr proprhs
        return [ forall' vars $ min' side ==> lhs === rhs | side <- [lhs,rhs] ]

-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Params -> Theory -> Prop -> [Prop] -> MakerM Property
theoryToInvocations params@(Params{..}) theory prop lemmas = do
    tr_lemmas <- lift $ mapM trLemma lemmas
    parts <- map (extendPart tr_lemmas) <$> prove params theory prop
    return $ Property
        { propName   = Thy.propName prop
        , propCode   = propRepr prop
        , propMatter = parts
        }


prove :: Params -> Theory -> Prop -> MakerM [Part]
prove Params{methods,indvars,indparts,indhyps,inddepth} Theory{..} prop@Prop{..} =
    sequence $ [ plainProof | 'p' `elem` methods ]
            ++ (do guard ('i' `elem` methods)
                   mapMaybe induction inductionCoords)

  where
    mkPart :: ProofMethod -> [Var] -> [Particle] -> Part
    mkPart meth ptrs particles = Part meth (deps,subthys,particles)
      where deps = map Function propFunDeps ++ map Pointer ptrs

    plainProof :: MakerM Part
    plainProof = do
        (neg_conj,ptrs) <- lift (capturePtrs unequals)
        let particle = Particle "plain" [comment "Proof by definitional equality"
                                        ,clause NegatedConjecture neg_conj]
        return (mkPart Plain ptrs [particle])
      where
        unequals :: HaloM Formula'
        unequals = do
            let vars = propVars
            lhs <- trExpr proplhs
            rhs <- trExpr proprhs
            return $ minrec lhs /\ minrec rhs /\ lhs =/= rhs

-- Induction ------------------------------------------------------------------

    inductionCoords :: [[Int]]
    inductionCoords =
        let var_indicies :: [Int]
            var_indicies = zipWith const [0..] propVars

            var_pow :: [[Int]]
            var_pow = drop 1 $ filterM (const [False,True]) var_indicies

        in  [ concat (replicate depth var_ixs)
            | var_ixs <- var_pow
            , length var_ixs <= indvars
            , depth <- [1..inddepth]
            ]

    induction :: [Int] -> Maybe (MakerM Part)
    induction coords = do
        let parts = structuralInduction tyEnv propVars coords

        -- If induction on these variables with this depth gives too many
        -- parts, then do not do this induction, return Nothing
        guard (length parts <= indparts)

        -- Some parts give very many hypotheses. If this is the case,
        -- we cruelly drop some of the first weak ones
        let dropHyps part = part { hypotheses =
                                      take indhyps (reverse $ hypotheses part) }

        return $ do
            -- Rename the variables
            parts' <- mapM (unVM getVar) parts

            -- Translate all induction parts to particles
            (particles,ptrs) <- lift $ capturePtrs $ sequence
                           [ Particle (show i) <$> trIndPart prop (dropHyps part)
                           | part <- parts'
                           | i <- [(0 :: Int)..] ]

            return (mkPart (Induction coords) ptrs particles)

trTerm :: Term DataCon Var -> CoreExpr
trTerm (Var x)    = C.Var x
trTerm (Con c as) = foldl C.App (C.Var (dataConWorkId c)) (map trTerm as)
trTerm (Fun f as) = foldl C.App (C.Var f) (map trTerm as)

ghcStyle :: Style DataCon Var Type
ghcStyle = Style
    { linc = P.text . showSDoc . ppr
    , linv = P.text . showSDoc . ppr
    , lint = P.text . showSDoc . ppr
    }

data Loc = Hyp | Concl

trIndPart :: Prop -> IndPart DataCon Var Type -> HaloM [Clause']
trIndPart Prop{..} ind_part@(IndPart skolem hyps concl) = do

    let trPred :: Loc -> [Term DataCon Var] -> HaloM (String,Formula')
        trPred loc tms = do
            lhs <- trExpr proplhs'
            rhs <- trExpr proprhs'
            let phi = case loc of
                    Hyp   -> min' lhs \/ min' rhs ==> lhs === rhs
                    Concl -> minrec rhs /\ minrec lhs /\ rhs =/= lhs
            return (showExpr proplhs' ++ "=" ++ showExpr proprhs',phi)
          where
            s = extendIdSubstList emptySubst
                   [ (v,trTerm t) | (v,_) <- propVars | t <- tms ]

            proplhs' = substExpr (text "trPred") s proplhs
            proprhs' = substExpr (text "trPred") s proprhs

        trHyp :: Hypothesis DataCon Var Type -> HaloM (String,Formula')
        trHyp (map fst -> qs,tms) = local (pushQuant qs)
             (second (forall' qs) <$> trPred Hyp tms)

        skolem_arities = M.fromList [ (sk,0) | (sk,_) <- skolem ]

    local (extendArities skolem_arities) $ do

        (str_hyp,tr_hyp) <- mapAndUnzipM
            (fmap (second (clause Hypothesis)) . trHyp) hyps

        (str_concl,tr_concl) <-
            second (clause NegatedConjecture) <$> trPred Concl concl

        return $
            comment (  "Proof by structural induction\n"
                    ++ unlines str_hyp ++ "|-\n" ++ str_concl
                    ++ "\n" ++ P.render (linPart ghcStyle ind_part))
            :tr_concl
            :tr_hyp
