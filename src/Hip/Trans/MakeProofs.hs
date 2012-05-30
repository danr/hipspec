{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns #-}
module Hip.Trans.MakeProofs where

import Hip.StructuralInduction
import Hip.StructuralInduction.Linearise
import Hip.Trans.ProofDatatypes
import Hip.Trans.Theory as Thy
import Hip.Trans.Types
import Hip.Params

import Halt.FOL.Abstract hiding (Term)
import Halt.ExprTrans
import Halt.Monad

import qualified Data.Map as M
import Data.Map (Map)

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
    tr_lemmas <- sequence [ Clause Lemma (propRepr lemma) <$> equals lemma
                          | lemma <- lemmas ]
    parts <- map (extendPart tr_lemmas) <$> prove params theory prop
    return $ Property { propName   = Thy.propName prop
                      , propCode   = propRepr prop
                      , propMatter = parts
                      }

equals :: Prop -> MakerM VarFormula
equals Prop{..} = lift $ local (pushQuant (map fst propVars)) $ do
    let vars = map fst propVars
    lhs <- trExpr proplhs
    rhs <- trExpr proprhs
    return (forall' vars (lhs === rhs))

prove :: Params -> Theory -> Prop -> MakerM [Part]
prove Params{methods} Theory{..} prop@Prop{..} =
    sequence $ [ plainProof | 'p' `elem` methods ]
            ++ (guard ('s' `elem` methods) >>
                map induction [ [i] | _ <- propVars | i <- [0..] ])

  where
    mkPart :: ProofMethod -> [Particle] -> Part
    mkPart meth particles = Part meth (thyDataAxioms,thyDefAxioms,particles)

    plainProof :: MakerM Part
    plainProof = do
         equality <- equals prop
         let particle = Particle "plain" [Clause Conjecture "plain" equality]
         return (mkPart Plain [particle])

    induction :: [Int] -> MakerM Part
    induction coords = do
        parts <- mapM (unVM getVar)
                      (structuralInduction tyEnv propVars coords)
        particles <- lift $ sequence
                                [ Particle (show i) <$> trIndPart prop part
                                | part <- parts | i <- [(0 :: Int)..] ]
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

trIndPart :: Prop -> IndPart DataCon Var Type -> HaltM [VarClause]
trIndPart Prop{..} ind_part@(IndPart skolem hyps concl) = do

   let skolem_arities = M.fromList [ (idName sk,0) | (sk,_) <- skolem ]

       trPred :: [Term DataCon Var] -> HaltM VarFormula
       trPred tms = (===) <$> trExpr lhs <*> trExpr rhs
         where
           s = extendIdSubstList emptySubst
                  [ (v,trTerm t) | (v,_) <- propVars | t <- tms ]

           lhs = substExpr (text "trPred") s proplhs
           rhs = substExpr (text "trPred") s proprhs

       trHyp :: Hypothesis DataCon Var Type -> HaltM VarFormula
       trHyp (map fst -> qs,tms) = local (pushQuant qs) (forall' qs <$> trPred tms)

   local (extendArities skolem_arities) $ do
       tr_hyp   <- mapM (fmap (Clause Hypothesis "hyp") . trHyp) hyps
       tr_concl <- Clause NegatedConjecture "conc" . neg <$> trPred concl
       return (tr_concl:tr_hyp)





