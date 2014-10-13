{-# LANGUAGE RecordWildCards, ScopedTypeVariables, NamedFieldPuns #-}
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
import HipSpec.Utils

import HipSpec.Lang.Monomorphise
import HipSpec.Lang.PolyFOL (trimDataDecls,uninterpretedInts)

import HipSpec.Lang.PrettyTFF (ppLemma,ppRecords)
import HipSpec.Lang.PrettyUtils (PP(..))
import Text.PrettyPrint (vcat,text)

import Data.Traversable (traverse)

-- import Text.Show.Pretty (ppShow)


import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Process (ProcessResult(..))

import Data.List
import Data.Maybe

import Control.Monad

-- import Jukebox.Toolbox (encodeString)

import Control.Exception (SomeException)
import qualified Control.Exception as E
import System.IO hiding (stdout,stderr)
import System.Process

encodeString :: String -> IO String
encodeString s = do
    (Just inh, Just outh, Just _errh, pid) <- createProcess $
        (proc "jukebox" ["fof","/dev/stdin"])
            { System.Process.std_in  = CreatePipe
            , System.Process.std_out = CreatePipe
            , System.Process.std_err = CreatePipe
            }
    (do
        hPutStr inh s
        hFlush inh
        hClose inh
        _exc <- waitForProcess pid
        out <- hGetContents outh
        length out `seq` return out)
      `E.catch` \ (e :: SomeException) -> do
        putStrLn ("Jukebox: " ++ show e)
        waitForProcess pid
        return ""

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
                . filter (\ x -> not (definitionalTheorem x) || add_stupid_lemmas)
                $ lemmas0

            enum_lemmas = zip [0..] lemmas

            lemma_theories = map (uncurry (trLemma arity_map)) enum_lemmas

            proof_tree = requireAny (map (requireAll . map Leaf) obligss)

            linTheory :: Theory -> HS LinTheory
            linTheory sthys = do
                let cls               = sortClauses False (concatMap clauses sthys)
                let (mcls,(ils,recs)) = first (sortClauses False) (monoClauses cls)
                let pp = PP (text . polyname) (text . polyname)
                let ui | any (`elem` provers) [CVC4,CVC4i,CVC4ig] = uninterpretedInts
                       | otherwise           = id
                let tff = ppTFF mcls
                debugWhen DebugMono $
                    "\nMonomorphising:\n" ++ ppTHF cls ++
                    "\n\nResult:\n" ++ ppTFF mcls ++
                    "\n\nLemmas:\n" ++ render' (vcat (map (ppLemma pp) ils)) ++
                    "\n\nRecords:\n" ++ render' (ppRecords pp recs)
                return $ LinTheory $ \ t -> case t of
                    AltErgoFmt     -> return $ ppAltErgo (sortClauses False cls)
                    AltErgoMonoFmt -> return $ ppMonoAltErgo mcls
                    MonoTFF        -> return tff
                    SMT            -> return $ ppSMT (ui (sortClauses True (trimDataDecls mcls)))
                    FOF            -> encodeString tff

            calc_dependencies :: Subtheory -> [Content]
            calc_dependencies s = concatMap dependencies (s:lemma_theories)

            fetcher :: [Content] -> [Subtheory]
            fetcher = trim (theory ++ lemma_theories)

            fetch_and_linearise :: Subtheory -> HS LinTheory
            fetch_and_linearise conj = linTheory $
                conj : lemma_theories ++ fetcher (calc_dependencies conj)

        proof_tree_lin :: Tree (Obligation eq LinTheory) <-
            traverse (traverse fetch_and_linearise) proof_tree

        let invoke_env = InvokeEnv
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
                    writeMsg UnknownResult
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
                    ByInduction{..} -> writeMsg InductiveProof
                        { property_name = prop_name thm_prop
                        , property_repr = maybePropRepr thm_prop
                        , used_lemmas   = fmap (map prop_name) thm_lemmas
                        , used_provers  = map show thm_provers
                        , vars          = ind_vars
                        }
            Nothing ->
                writeMsg FailedProof
                    { property_name = prop_name prop
                    , property_repr = maybePropRepr prop
                    }

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
        mkProof pf = Just Theorem
            { thm_prop = prop
            , thm_proof = pf
            , thm_provers = nub $ map (fst . ob_content) grp
            , thm_lemmas
                = fmap (map lemma_lkup . nub . concat)
                $ mapM (successLemmas . snd . ob_content) grp
            }
  where

    resType ObInduction{..} = ind_coords

    results' = [ ob | ob@Obligation{..} <- results
                    , prop_name prop == prop_name ob_prop
                    , isSuccess (snd ob_content)
               ]

    proofs :: [[Obligation eq Result]]
    proofs = filter check $ groupSortedOn (resType . ob_info) results'

    check :: [Obligation eq Result] -> Bool
    check grp@(Obligation _ (ObInduction _ _ nums) _:_) =
        all (\ n -> any ((n ==) . ind_num . ob_info) grp) [0..nums-1]
    check _ = False

