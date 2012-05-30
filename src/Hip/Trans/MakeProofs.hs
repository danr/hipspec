{-# LANGUAGE RecordWildCards,TupleSections #-}
module Hip.Trans.MakeProofs where

import Hip.Trans.TranslateExpr
import Hip.Trans.TranslateDecl
import Hip.Trans.Core
import Hip.Trans.Constructors
import Hip.Trans.Monad
import Hip.Trans.Pretty
import Hip.Trans.ProofDatatypes
import Hip.Trans.NecessaryDefinitions
import Hip.Trans.FixpointInduction
import Hip.Trans.Types
import Hip.Trans.Theory
import Hip.Trans.TyEnv
import Hip.Trans.TranslateExpr
import qualified Hip.StructuralInduction as S
import Hip.StructuralInduction.Linearise
import Hip.Util (putEither,concatMapM)
import Hip.Messages
import Hip.Params

import Language.TPTP hiding (Decl,Var,VarName,declName)
import Language.TPTP.Pretty
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

import Data.List
import Data.Maybe (fromMaybe,mapMaybe)
import Control.Arrow ((&&&),first)

import Data.Set (Set)
import qualified Data.Set as S

powerset :: [a] -> [[a]]
powerset = init . filterM (const [True,False])

makeProofDecls :: TyEnv -> Params -> Theory -> Prop -> [Prop] -> [TM Part]
makeProofDecls env params theory prop@(Prop{..}) lemmas =
    let typedVars = case propType of TyApp ts -> zip propVars ts
                                     _        -> []

        resTy     = unProp (resType propType)

        fundecls  = theoryFunDecls theory

        recfuns   = theoryRecFuns theory

    in  prove env params fundecls recfuns resTy propName typedVars proplhs proprhs

prove :: TyEnv
      -- ^ The type environment
      -> Params
      -- ^ The parameters to the program
      -> [Decl]
      -- ^ The function definitions in the file. The reason why this is
      --   here is because fixpoint induction needs to change some definitions
      -> Set Name
      -- ^ Which functions are recursive. Needed for fixpoint induction
      -> Type
      -- ^ The result type of the property
      -> Name
      -- ^ Name of the property
      -> [(Name,Type)]
      -- ^ Arguments together with type
      -> Expr
      -- ^ LHS
      -> Expr
      -- ^ RHS
      -> [TM Part]
      -- ^ Resulting instructions how to do proof declarations for this
prove env params@(Params{..}) fundecls recfuns resTy fname typedVars lhs rhs =
    let indargs :: [(Name,Type)]
        indargs = filter (\(_,t) -> concreteType t) typedVars
        powset :: [[(Name,Type)]]
        powset = powerset indargs
   in  concat $ [ plainProof | 'p' `elem` methods ]
             ++ [ map (proofByStructInd False d)
                      (filter ((<=indvars) .  length) powset)
                | d <- [1..inddepth], 'i' `elem` methods ]

  where
    accompanyParts :: ProofMethod -> Coverage -> TM [Particle] -> TM Part
    accompanyParts prooftype coverage partsm = do
        let funs = map (declName &&& length . declArgs) fundecls
        parts  <- partsm
        return $ Part { partMethod     = prooftype
                      , partCoverage   = coverage
                      , partMatter     = ([],parts)
                      }

    plainProof :: [TM Part]
    plainProof = return $ accompanyParts Plain Infinite $ locally $ do
                     lhs' <- translateExpr lhs
                     rhs' <- translateExpr rhs
                     tytms <- mapM (\(n,t) -> (,t) <$> translateExpr (Var n)) typedVars
                     p <- forallUnbound (typeGuards env tytms (lhs' === rhs'))
                     return $ [ Particle "plain" [Conjecture "plain" p] ]

    proofByStructInd :: Bool -> Int -> [(Name,Type)] -> TM Part
    proofByStructInd addBottom d ns = accompanyParts
      (StructuralInduction (map fst ns) addBottom d)
      (if addBottom then Infinite else Finite) $ do
        env <- translateEnv <$> getEnv addBottom

        let parts = S.structuralInduction env ns (concat (replicate d [0..length ns-1]))

        if length parts > 0 && (length parts <= indsteps || indsteps == 0)
          then forM parts $ \part -> locally $ do
                  let part' = S.unV (\s i -> s ++ "_" ++ show i) part
                  (tr_hyps,tr_conj) <- skFormula part'
                  popQuantified -- ugh
                  return $ Particle { particleDesc   = intercalate "_" (map ppTerm (S.consequent part))
                                    , particleMatter = Conjecture "conj" tr_conj
                                                     : map (Hypothesis "hyp") tr_hyps
                                    }
          else return []
      where
        instP :: [Expr] -> TM T.Formula
        instP es = locally $ do
            zipWithM_ addIndirection (map fst ns) es
            lhs' <- translateExpr lhs
            rhs' <- translateExpr rhs
            tytms <- mapM (\(n,t) -> (,t) <$> translateExpr (Var n)) typedVars
            forallUnbound (typeGuards env tytms (lhs' === rhs'))

        skFormula :: S.Formula Name Name Type -> TM ([T.Formula],T.Formula)
        skFormula f = case f of
            S.Forall xts phi -> do
                     addFuns (zip (map fst xts) (repeat 0))
                     skFormula phi
            phis S.:=> psi -> liftM2 (,) (mapM trFormula phis) (trFormula psi)
            S.P tms -> liftM ([],) (trFormula f)


        trFormula :: S.Formula Name Name Type -> TM T.Formula
        trFormula f = case f of
            S.Forall xts phi -> do
                     xs <- forM xts $ \(x,_) -> bindMeQuantPlease x
                     phi' <- trFormula phi
                     tytms <- mapM (\(n,t) -> (,t) <$> translateExpr (Var n)) xts
                     return $ forall' xs (typeGuards env tytms phi')
            phis S.:=> psi   -> liftM2 (===>) (mapM trFormula phis) (trFormula psi)
            S.P tms          -> instP (map trTerm tms)

        trTerm :: S.Term Name Name -> Expr
        trTerm tm = case tm of
             S.Var x     -> Var x
             S.Con c tms -> Con c (map trTerm tms)
             S.Fun f tms -> App f (map trTerm tms)


-- These were added since StructuralInduction sometimes returns empty
-- parts because it overflowed the number allowed hyps or steps, and
-- this was inside the monad so this was the easiest fix, but yes -
-- an Ugly Hack!
removeEmptyParts :: Property -> Property
removeEmptyParts (Property n c parts)
  = Property n c (filter (not . null . snd . partMatter) parts)

-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Params -> Theory -> Prop -> [Prop] -> (Property,[Msg])
theoryToInvocations params@(Params{..}) theory prop@(Prop{..}) lemmas =
    let tyEnv  = theoryTyEnv theory
        partsm = makeProofDecls tyEnv params theory prop lemmas
        (parts,dbg) = unzip $ flip map partsm $ \partm -> runTM params $ do
                        wdproof $ propName
                        addCons (thyDatas theory)
                        let funs = map (declName &&& length . declArgs) (theoryFunDecls theory)
                        addFuns funs
                        part <- partm
                        lemmaTPTP <- zipWithM translateLemma [0..] lemmas
                        mapM_ (uncurry registerFunPtr) (theoryUsedPtrs theory)
                        extra    <- envStDecls
                        let tyaxioms = concat [ mapMaybe (infDomainAxiom tyEnv)
                                                         (theoryDataTypes theory)
                                              | not thy_no_infdom ]
                                    ++ concat [ anyTypeAxiom :
                                                map (genTypePred tyEnv)
                                                    (theoryDataTypes theory)
                                              | not thy_no_typreds ]
                        db    <- popMsgs
                        return (extendPart (extra ++ tyaxioms ++ theoryFunTPTP theory ++ lemmaTPTP) part,db)
        property = Property { propName   = propName
                            , propCode   = propRepr
                            , propMatter = parts
                            }
    in (removeEmptyParts property,concat dbg)

