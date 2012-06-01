{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns #-}
module Hip.Trans.MakeProofs where

import Hip.StructuralInduction
import Hip.StructuralInduction.Linearise
import Hip.Trans.ProofDatatypes
import Hip.Trans.Theory as Thy
import Hip.Trans.Types
import Hip.Params

import qualified Halt.FOL.Abstract as A
import Halt.FOL.Abstract hiding (Term,Lemma)
import Halt.ExprTrans
import Halt.Monad
import Halt.Util
import Halt.Subtheory

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (mapMaybe)

import Control.Arrow
import Control.Applicative
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
import Outputable (text)

import qualified Text.PrettyPrint as P

type MakerM = StateT (UniqSupply,Map (Var,Integer) Var) HaltM

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

runMakerM :: HaltEnv -> UniqSupply -> MakerM a -> ((a,[String]),UniqSupply)
runMakerM env us mm = let ((hm,(us',_)),msg) = runHaltM env (runStateT mm (us,M.empty))
                      in  ((hm,msg),us')


-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Params -> Theory -> Prop -> [Prop] -> MakerM Property
theoryToInvocations params@(Params{..}) theory prop lemmas = do
    tr_lemmas <- sequence [ Subtheory (Lemma (propRepr lemma) (propDeps lemma))
                                      [] "" . (:[]) <$> equals lemma
                          | lemma <- lemmas ]
    parts <- map (extendPart tr_lemmas) <$> prove params theory prop
    return $ Property { propName   = Thy.propName prop
                      , propCode   = propRepr prop
                      , propMatter = parts
                      }

equals :: Prop -> MakerM Formula'
equals Prop{..} = lift $ local (pushQuant (map fst propVars)) $ do
    let vars = map fst propVars
    lhs <- trExpr proplhs
    rhs <- trExpr proprhs
    return (forall' vars (lhs === rhs))

prove :: Params -> Theory -> Prop -> MakerM [Part]
prove Params{methods,indvars,indparts,indhyps,inddepth} Theory{..} prop@Prop{..} =
    sequence $ [ plainProof | 'p' `elem` methods ]
            ++ (do guard ('i' `elem` methods)
                   mapMaybe induction inductionCoords)

  where
    mkPart :: ProofMethod -> [Particle] -> Part
    mkPart meth particles = Part meth (propDeps,subthys,particles)

    plainProof :: MakerM Part
    plainProof = do
        equality <- equals prop
        let particle = Particle "plain" [clause Conjecture equality]
        return (mkPart Plain [particle])

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
            particles <- lift $ sequence
                           [ Particle (show i) <$> trIndPart prop (dropHyps part)
                           | part <- parts' | i <- [(0 :: Int)..] ]

            return (mkPart (StructuralInduction coords) particles)

-- Induction ------------------------------------------------------------------

trTerm :: Term DataCon Var -> CoreExpr
trTerm (Var x)    = C.Var x
trTerm (Con c as) = foldl C.App (C.Var (dataConWorkId c)) (map trTerm as)
trTerm (Fun f as) = foldl C.App (C.Var f) (map trTerm as)

ghcStyle :: Style DataCon Var Type
ghcStyle = Style { linc = const (P.text "c")
                 , linv = const (P.text "v")
                 , lint = const P.empty
                 }

trIndPart :: Prop -> IndPart DataCon Var Type -> HaltM [Clause']
trIndPart Prop{..} ind_part@(IndPart skolem hyps concl) = do

   let skolem_arities = M.fromList [ (idName sk,0) | (sk,_) <- skolem ]

       trPred :: [Term DataCon Var] -> HaltM Formula'
       trPred tms = (===) <$> trExpr lhs <*> trExpr rhs
         where
           s = extendIdSubstList emptySubst
                  [ (v,trTerm t) | (v,_) <- propVars | t <- tms ]

           lhs = substExpr (text "trPred") s proplhs
           rhs = substExpr (text "trPred") s proprhs

       trHyp :: Hypothesis DataCon Var Type -> HaltM Formula'
       trHyp (map fst -> qs,tms) = local (pushQuant qs) (forall' qs <$> trPred tms)

   local (extendArities skolem_arities) $ do
       tr_hyp   <- mapM (fmap (clause Hypothesis) . trHyp) hyps
       tr_concl <- clause NegatedConjecture . neg <$> trPred concl
       return (tr_concl:tr_hyp)





