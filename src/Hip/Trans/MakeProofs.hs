{-# LANGUAGE RecordWildCards,NamedFieldPuns,TupleSections #-}
module Hip.Trans.MakeProofs where

import Hip.Trans.ProofDatatypes
import Hip.Trans.Theory as Thy

import Hip.StructuralInduction
import Hip.Params

import Halt.FOL.Abstract
import Halt.ExprTrans
import Halt.Monad

import Control.Applicative
import Control.Monad.Reader

type MakerM = HaltM

runMakerM :: HaltEnv -> HaltM a -> (a,[String])
runMakerM = runHaltM

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
equals Prop{proplhs,proprhs,propVars} = local (pushQuant (map fst propVars)) $ do
    let vars = map fst propVars
    lhs <- trExpr proplhs
    rhs <- trExpr proprhs
    return (forall' vars (lhs === rhs))

prove :: Params -> Theory -> Prop -> MakerM [Part]
prove Params{methods} Theory{..} prop =
    sequence [ plainProof | 'p' `elem` methods ]
  where
    plainProof :: MakerM Part
    plainProof = do
         equality <- equals prop
         let particle = Particle "plain" [Clause Conjecture "plain" equality]
         return $ Part Plain (thyDataAxioms,thyDefAxioms,[particle])




