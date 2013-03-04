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
import HipSpec.Trans.TypeGuards
import HipSpec.Trans.Lemma
import HipSpec.Trans.MakerMonad

import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Process (ProcessResult(..))

import Halo.Monad
import Halo.Subtheory
import Halo.Trim
import Halo.Util

import Halo.FOL.Abstract hiding (definitions)
import Halo.FOL.Dump
import Halo.FOL.Linearise
import Halo.FOL.LineariseSMT
import Halo.FOL.Operations
import Halo.FOL.RemoveMin
import Halo.FOL.Rename

import Data.List
import Data.Either
import Data.Maybe

import Control.Monad

import UniqSupply

-- | Try to prove some properties in a theory, given some lemmas
tryProve :: forall eq . [Property eq] -> [Theorem eq]
         -> HS ([Theorem eq],[Property eq])
tryProve []    _                         = return ([],[])
tryProve props (map thm_prop -> lemmas0) = do

    us <- liftIO $ mkSplitUniqSupply 'c'

    Info{..} <- getInfo
    let Params{..} = params

    let lemmas
            | isolate = filter (not . isUserStated) lemmas0
            | otherwise = lemmas0

        enum_lemmas = zip [0..] lemmas

        (lemma_theories,_) = runHaloM halo_env $
            mapM (uncurry $ flip translateLemma) enum_lemmas

        ((proof_tree,_),_) = runMakerM halo_env us $
            tryAll <$> mapM (makeProofs params) props

        style_conf = StyleConf
             { style_comments   = comments
             , style_cnf        = cnf
             , style_dollar_min = False
             }

        toTPTP :: [Clause'] -> String
        toTPTP
            | readable_tptp = linStrStyleTPTP style_conf . fst . renameClauses
            | otherwise     = dumpTPTP

        linTheory :: [HipSpecSubtheory] -> LinTheory
        linTheory
            = (\ cls -> LinTheory $ \ t ->
                let smt_str = linSMT cls
                in  case t of
                        TPTP         -> toTPTP cls
                        SMT          -> smt_str
                        SMTUnsatCore -> addUnsatCores smt_str)
            . map (clauseMapFormula typeGuardFormula)
            . (not use_min ? removeMins)
            . concatMap toClauses

        calc_dependencies :: HipSpecSubtheory -> [HipSpecContent]
        calc_dependencies s = concatMap depends (s:lemma_theories)
            ++ [ Specific BottomAxioms | bottoms ]

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

    let check :: [Obligation eq Result] -> Bool
        check grp@(Obligation _ (Induction _ _ nums) _:_) =
            all (\ n -> any ((n ==) . ind_num . ob_info) grp) [0..nums-1]
        check [] = error "MakeInvocations: check (impossible)"

        results :: ([Theorem eq],[Property eq])
        results@(thms,conjs) = partitionEithers

            [
                let proofs :: [[Obligation eq Result]]
                    proofs
                        = filter check
                        $ groupSortedOn (ind_coords . ob_info)
                                [ ob | ob@Obligation{..} <- result
                                     , prop == ob_prop
                                     , success (snd $ ob_content)
                                ]

                in  case proofs of
                        [] -> Right prop
                        grp:_ -> case grp of
                            [] -> error "MakeInvocations: results (impossible)"
                            Obligation _ (Induction cs _ _) _:_
                                -> Left $ Theorem
                                    { thm_prop = prop
                                    , thm_proof = ByInduction (varsFromCoords prop cs)
                                    , thm_provers = nub $ map (fst . ob_content) grp
                                    , thm_lemmas
                                        = fmap ( map (fromJust . flip lookup enum_lemmas)
                                               . nub
                                               . concat
                                               )
                                        $ sequence
                                        $ map (successLemmas . snd . ob_content) grp
                                    }

            | prop <- props
            ]

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

    mapM_ (writeMsg . FailedProof . propName) conjs

    return results

