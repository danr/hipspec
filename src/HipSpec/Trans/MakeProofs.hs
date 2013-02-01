{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns #-}
module HipSpec.Trans.MakeProofs where

import Induction.Structural

import HipSpec.Trans.ProofDatatypes
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop
import HipSpec.Trans.Types
import HipSpec.Trans.TypeGuards
import HipSpec.Params

import Halo.FOL.Abstract hiding (Term)
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
import Control.Monad.Error

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
runMakerM env us mm
    = case runHaloMsafe env (runStateT mm (us,M.empty)) of
        (Right ((hm,(us',_))),msg) -> ((hm,msg),us')
        (Left err,_msg)
            -> error $ "Halo.Trans.MakeProofs.runMakerM, halo says: " ++ err

trLemma :: Prop -> HaloM HipSpecSubtheory
trLemma lemma@Prop{..} = do
    (tr_lem,ptrs) <- capturePtrs equals
    return $ Subtheory
        { provides    = Specific (Lemma propRepr)
        , depends     = map Function propFunDeps ++ ptrs
        , description = "Lemma " ++ propRepr
                        ++ "\ndependencies: " ++ unwords (map idToStr propFunDeps)
        , formulae    = tr_lem
        }
  where
    equals :: HaloM [Formula']
    equals = do
        (lhs,rhs) <- trEquality propEquality
        assums <- mapM trEquality' propAssume
        return [ foralls $ min' side ==> (assums ===> lhs === rhs) | side <- [lhs,rhs] ]

trEquality :: Equality -> HaloM (Term',Term')
trEquality (e1 :== e2) = liftM2 (,) (trExpr e1) (trExpr e2)

trEquality' :: Equality -> HaloM Formula'
trEquality' = liftM (uncurry (===)) . trEquality

-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Params -> Theory -> Prop -> [Prop] -> MakerM Property
theoryToInvocations params@(Params{..}) theory prop lemmas = do
    tr_lemmas <- lift $ mapM trLemma lemmas
    parts <- map (extendPart tr_lemmas) <$> prove params theory prop
    return $ Property
        { propName   = Prop.propName prop
        , propCode   = propRepr prop
        , propMatter = parts
        }


prove :: Params -> Theory -> Prop -> MakerM [Part]
prove Params{methods,indvars,indparts,indhyps,inddepth} Theory{..} prop@Prop{..} =
    (sequence $ [ plainProof | 'p' `elem` methods ]
            ++ (do guard ('i' `elem` methods)
                   mapMaybe induction inductionCoords))
      `catchError` \err -> do
          lift $ cleanUpFailedCapture
          return []

  where
    mkPart :: ProofMethod -> [HipSpecContent] -> [Particle] -> Part
    mkPart meth ptr_content particles = Part meth (deps,subthys,particles)
      where deps = map Function propFunDeps ++ ptr_content

    plainProof :: MakerM Part
    plainProof = do
        (neg_conj,ptrs) <- lift (capturePtrs unequals)
        let particle = Particle "plain" $
                comment "Proof by definitional equality" : axioms neg_conj
        return (mkPart Plain ptrs [particle])
      where
        unequals :: HaloM [Formula']
        unequals = local (addSkolems $ map fst propVars) $ do
            (lhs,rhs) <- trEquality propEquality
            assums <- mapM trEquality' propAssume
            return $
                [minrec lhs,minrec rhs,lhs =/= rhs] ++
                assums ++
                mapMaybe (typeGuardSkolem . fst) propVars


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
        let parts = subtermInductionQ tyEnv propVars coords

        -- If induction on these variables with this depth gives too many
        -- parts, then do not do this induction, return Nothing
        guard (length parts <= indparts)

        -- Some parts give very many hypotheses. If this is the case,
        -- we cruelly drop some of the first weak ones
        let dropHyps part = part
                { hypotheses = take indhyps (reverse $ hypotheses part) }

        return $ do
            -- Rename the variables
            parts' <- mapM (unTagM getVar) parts

            -- Translate all induction parts to particles
            (particles,ptrs) <- lift $ capturePtrs $ sequence
                           [ Particle (show i) <$> trObligation prop (dropHyps part)
                           | part <- parts'
                           | i <- [(0 :: Int)..] ]

            return (mkPart (Induction coords) ptrs particles)

trTerm :: Term DataCon Var -> CoreExpr
trTerm (Var x)    = C.Var x
trTerm (Con c as) = foldl C.App (C.Var (dataConWorkId c)) (map trTerm as)
trTerm (Fun f as) = foldl C.App (C.Var f) (map trTerm as)

ghcStyle :: Style DataCon Var Type
ghcStyle = Style
    { linc = P.text . showOutputable
    , linv = P.text . showOutputable
    , lint = P.text . showOutputable
    }

data Loc = Hyp | Concl

trObligation :: Prop -> Obligation DataCon Var Type -> HaloM [Clause']
trObligation Prop{..} obligation@(Obligation skolem hyps concl) = do

    let trPred :: Loc -> [Term DataCon Var] -> HaloM (String,Formula')
        trPred loc tms = do
            (lhs,rhs) <- trEquality propEquality'
            assums <- mapM trEquality' propAssume'
            let phi = case loc of
                    Hyp   -> min' lhs \/ min' rhs ==> (assums ===> lhs === rhs)
                    Concl -> ands $ [minrec rhs,minrec lhs,rhs =/= lhs] ++ assums
            return (show propEquality',phi)
          where
            s = extendIdSubstList emptySubst
                    [ (v,trTerm t) | (v,_) <- propVars | t <- tms ]

            propEquality':propAssume' = flip map (propEquality:propAssume) $ \ eq -> case eq of
                e1 :== e2 -> substExpr (text "trPred") s e1 :== substExpr (text "trPred") s e2

        trHyp :: Hypothesis DataCon Var Type -> HaloM (String,Formula')
        trHyp (map fst -> qs,tms) = second foralls <$> trPred Hyp tms

        skolem_vars = map fst skolem

    local (addSkolems skolem_vars) $ do

        (str_hyp,tr_hyp) <- mapAndUnzipM
            (fmap (second (clause hypothesis)) . trHyp) hyps

        (str_concl,tr_concl) <-
            second (axioms . splitFormula) <$> trPred Concl concl

        return
            $ comment ( "Proof by structural induction\n" ++
                        unlines str_hyp ++ "|-\n" ++ str_concl ++
                        "\n" ++ P.render (linObligation ghcStyle obligation) )
            : comment "Conclusion" : tr_concl
            ++ comment "Hypothesis" : tr_hyp
            ++ comment "Type guards" :
                axioms (mapMaybe typeGuardSkolem skolem_vars)
