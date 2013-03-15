{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
module HipSpec.MakeInvocations (tryProve) where


import HipSpec.Monad
import HipSpec.ATP.Invoke
import HipSpec.ATP.Provers
import HipSpec.ATP.Results
import HipSpec.Trans.MakeProofs
import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.Lemma
import HipSpec.Trans.MakerMonad

import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Process (ProcessResult(..))

import Halo.Monad
import Halo.Trim
import Halo.Util

import Halo.FOL.LineariseSMT

import Data.List
import Data.Either
import Data.Maybe

import Control.Monad

import UniqSupply

-- | Filters away definitional theorems (those that didn't need induction to be
--   proved)
interestingLemmas :: [Theorem eq] -> [Property eq]
interestingLemmas = map thm_prop . filter (not . definitionalTheorem)

-- | Try to prove some properties in a theory, given some lemmas
tryProve :: forall eq . [Property eq] -> [Theorem eq]
         -> HS ([Theorem eq],[Property eq])
tryProve props (interestingLemmas -> lemmas0) = do

    us <- liftIO $ mkSplitUniqSupply 'c'

    Info{..} <- getInfo
    let Params{..} = params

    case fst $ runMakerM halo_env us (catMaybes <$> mapM (makeProofs params) props) of

        ([],msgs)        -> do
            liftIO $ mapM_ putStrLn msgs
            return ([],props)
        (proof_trees,_msgs) -> do

            let lemmas
                    | isolate = filter (not . isUserStated) lemmas0
                    | otherwise = lemmas0

                enum_lemmas = zip [0..] lemmas

                (lemma_theories,_) = runHaloM halo_env $
                    mapM (uncurry $ flip translateLemma) enum_lemmas

                proof_tree = tryAll proof_trees

                linTheory :: [HipSpecSubtheory] -> LinTheory
                linTheory sthys = LinTheory $ \ t -> case t of
                    TPTP         -> "no tptp!"
                    SMT          -> smt_str
                    SMTUnsatCore -> addUnsatCores smt_str
                  where
                    smt_str = linSMT
                        (concatMap toClauses sthys)
                        (nubSortedOn fst (concatMap typedecls sthys))
                        (nubSortedOn fst (concatMap datadecls sthys))

                calc_dependencies :: HipSpecSubtheory -> [HipSpecContent]
                calc_dependencies s = concatMap depends (s:lemma_theories)

                fetcher :: [HipSpecContent] -> [HipSpecSubtheory]
                fetcher = trim (subthys theory ++ lemma_theories)

                fetch_and_linearise :: HipSpecSubtheory -> LinTheory
                fetch_and_linearise conj = linTheory $
                    conj : lemma_theories ++ fetcher (calc_dependencies conj)

                proof_tree_lin :: Tree (Obligation eq LinTheory)
                proof_tree_lin = fmap (fmap fetch_and_linearise) proof_tree

                env = Env
                    { timeout         = timeout
                    , store           = output
                    , provers         = proversFromString provers
                    , processes       = processes
                    , z_encode        = z_encode_filenames
                    }

            result :: [Obligation eq Result] <- invokeATPs proof_tree_lin env

            let lemma_lkup :: Int -> Property eq
                lemma_lkup = fromJust . flip lookup enum_lemmas

                results :: ([Theorem eq],[Property eq])
                results@(thms,conjs)
                    = partitionEithers $ map (resultsForProp lemma_lkup result) props

            forM_ result $ \ Obligation{..} -> do
                let (prover,res) = ob_content
                case res of
                    Unknown ProcessResult{..} ->
                        writeMsg $ UnknownResult
                            { prop_name    = propName ob_prop
                            , prop_ob_info = ob_info
                            , used_prover  = show prover
                            , m_stdout     = stdout
                            , m_stderr     = stderr
                            , m_excode     = show excode
                            }
                    _ -> return ()

            forM_ thms $ \ Theorem{..} -> case thm_proof of
                ByInduction{..} -> writeMsg $ InductiveProof
                    { prop_name    = propName thm_prop
                    , used_lemmas  = fmap (map propName) thm_lemmas
                    , used_provers = map show thm_provers
                    , vars         = ind_vars
                    }
                ByApproxLemma -> writeMsg $ ApproxProof
                    { prop_name    = propName thm_prop
                    , used_lemmas  = fmap (map propName) thm_lemmas
                    , used_provers = map show thm_provers
                    }


            mapM_ (writeMsg . FailedProof . propName) conjs

            return results

resultsForProp :: forall eq . (Int -> Property eq)
               -> [Obligation eq Result] -> Property eq
               -> Either (Theorem eq) (Property eq)
resultsForProp lemma_lkup results prop = case proofs of
    [] -> Right prop
    grp:_ -> case grp of
        [] -> error "MakeInvocations: results (impossible)"
        Obligation _ ApproxLemma _:_ -> mkProof ByApproxLemma
        Obligation _ (Induction cs _ _) _:_ -> mkProof (ByInduction (varsFromCoords prop cs))
      where
        mkProof pf = Left $ Theorem
            { thm_prop = prop
            , thm_proof = pf
            , thm_provers = nub $ map (fst . ob_content) grp
            , thm_lemmas
                = fmap ( map lemma_lkup . nub . concat)
                $ sequence
                $ map (successLemmas . snd . ob_content) grp
            }
  where

    resType (Induction{..}) = Right ind_coords
    resType ApproxLemma     = Left ()

    results' = [ ob | ob@Obligation{..} <- results
                    , prop == ob_prop
                    , success (snd $ ob_content)
               ]

    proofs :: [[Obligation eq Result]]
    proofs = filter check $ groupSortedOn (resType . ob_info) results'

    check :: [Obligation eq Result] -> Bool
    check [Obligation _ ApproxLemma _] = True
    check grp@(Obligation _ (Induction _ _ nums) _:_) =
        all (\ n -> any ((n ==) . ind_num . ob_info) grp) [0..nums-1]
    check _ = False

