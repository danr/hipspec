{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns, ScopedTypeVariables, NamedFieldPuns #-}
module HipSpec.MakeInvocations (tryProve) where

import HipSpec.ATP.Invoke
import HipSpec.ATP.Provers
import HipSpec.ATP.Results

import HipSpec.Monad
import HipSpec.MakeProofs
import HipSpec.ThmLib
import HipSpec.Theory
import HipSpec.Property
import HipSpec.Lemma
import HipSpec.Trim
import HipSpec.Util

import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Process (ProcessResult(..))

import Data.List
import Data.Maybe

import Control.Monad

-- | Try to prove a property, given some lemmas
tryProve :: forall eq . Property eq -> [Theorem eq] -> HS (Maybe (Theorem eq))
tryProve prop lemmas0 = do

    Params{..} <- getParams

    obligss <- makeProofs prop

    if null obligss || any null obligss then return Nothing else do

        Env{theory,arity_map} <- getEnv

        let isolation
                | isolate   = not . isUserStated
                | otherwise = const True

            lemmas
                = filter isolation
                . map thm_prop
                . filter (not . definitionalTheorem)
                $ lemmas0

            enum_lemmas = zip [0..] lemmas

            lemma_theories = map (uncurry (trLemma arity_map)) enum_lemmas

            proof_tree = requireAny (map (requireAll . map Leaf) obligss)

            linTheory :: Theory -> LinTheory
            linTheory sthys = LinTheory $ \ t -> case t of
                AltErgoFmt -> ppAltErgo (sortClauses (concatMap clauses sthys))

            calc_dependencies :: Subtheory -> [Content]
            calc_dependencies s = concatMap dependencies (s:lemma_theories)

            fetcher :: [Content] -> [Subtheory]
            fetcher = trim (theory ++ lemma_theories)

            fetch_and_linearise :: Subtheory -> LinTheory
            fetch_and_linearise conj = linTheory $
                conj : lemma_theories ++ fetcher (calc_dependencies conj)

            proof_tree_lin :: Tree (Obligation eq LinTheory)
            proof_tree_lin = fmap (fmap fetch_and_linearise) proof_tree

            invoke_env = InvokeEnv
                { timeout         = timeout
                , store           = output
                , provers         = proversFromNames provers
                , processes       = processes
                , z_encode        = z_encode_filenames
                }

        results :: [Obligation eq Result] <- invokeATPs proof_tree_lin invoke_env

        forM_ results $ \ Obligation{..} -> do
            let (prover,res) = ob_content
            case res of
                Unknown ProcessResult{..} ->
                    writeMsg $ UnknownResult
                        { property_name = prop_name ob_prop
                        , prop_ob_info  = ob_info
                        , used_prover   = show prover
                        , m_stdout      = stdout
                        , m_stderr      = stderr
                        , m_excode      = show excode
                        }
                _ -> return ()

        let lemma_lkup :: Int -> Property eq
            lemma_lkup = fromJust . flip lookup enum_lemmas

            res = resultsForProp lemma_lkup results prop

        case res of
            Just Theorem{..} ->
                case thm_proof of
                    ByInduction{..} -> writeMsg $ InductiveProof
                        { property_name = prop_name thm_prop
                        , used_lemmas   = fmap (map prop_name) thm_lemmas
                        , used_provers  = map show thm_provers
                        , vars          = ind_vars
                        }
            Nothing ->
                writeMsg . FailedProof . prop_name $ prop

        return res

resultsForProp :: forall eq . (Int -> Property eq)
               -> [Obligation eq Result] -> Property eq
               -> Maybe (Theorem eq)
resultsForProp lemma_lkup results prop = case proofs of
    []    -> Nothing
    grp:_ -> case grp of
        [] -> error "MakeInvocations: results (impossible)"
        Obligation _ (ObInduction cs _ _) _:_ ->
            mkProof (ByInduction (varsFromCoords prop cs))
      where
        mkProof pf = Just $ Theorem
            { thm_prop = prop
            , thm_proof = pf
            , thm_provers = nub $ map (fst . ob_content) grp
            , thm_lemmas
                = fmap ( map lemma_lkup . nub . concat)
                $ sequence
                $ map (successLemmas . snd . ob_content) grp
            }
  where

    resType ObInduction{..} = ind_coords

    results' = [ ob | ob@Obligation{..} <- results
                    , prop_name prop == prop_name ob_prop
                    , success (snd $ ob_content)
               ]

    proofs :: [[Obligation eq Result]]
    proofs = filter check $ groupSortedOn (resType . ob_info) results'

    check :: [Obligation eq Result] -> Bool
    check grp@(Obligation _ (ObInduction _ _ nums) _:_) =
        all (\ n -> any ((n ==) . ind_num . ob_info) grp) [0..nums-1]
    check _ = False

