{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
module HipSpec.MakeInvocations
    ( tryProve
    , InvokeResult(..)
    , partitionInvRes
--    , parLoop
--    , printInfo
    ) where

import HipSpec.Monad
import HipSpec.ATP.Invoke
import HipSpec.ATP.Provers
import HipSpec.ATP.Results
import HipSpec.Trans.MakeProofs
import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.TypeGuards

import Control.Concurrent.STM.Promise.Tree

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

import Control.Monad

import UniqSupply

-- remove ByInduction, express it as vars = []
data InvokeResult
    = ByInduction { invoke_lemmas :: Maybe [String], provers :: [ProverName], vars :: [String] }
    | ByPlain     { invoke_lemmas :: Maybe [String], provers :: [ProverName] }
    | NoProof
  deriving (Eq,Ord,Show)

partitionInvRes :: [(a,InvokeResult)] -> ([a],[a],[a])
partitionInvRes []          = ([],[],[])
partitionInvRes ((x,ir):xs) = case ir of
    ByInduction{} -> (x:a,b,c)
    ByPlain{}     -> (a,x:b,c)
    NoProof{}     -> (a,b,x:c)
  where (a,b,c) = partitionInvRes xs

-- | Try to prove some properties in a theory, given some lemmas
tryProve :: forall eq . [Property eq] -> [Property eq] -> HS [(Property eq,InvokeResult)]
tryProve []    _       = return []
tryProve props lemmas0 = do

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
             , style_cnf        = not fof
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
            , lemma_lookup    = \ n -> fmap propRepr (lookup n enum_lemmas)
            , store           = output
            , provers         = proversFromString provers
            , processes       = processes
            , z_encode        = z_encode_filenames
            }

    result :: [Obligation eq Result] <- invokeATPs proof_tree_lin env

    -- print result

    let check :: [Obligation eq Result] -> Bool
        check grp@(Obligation _ (Induction _ _ nums) _:_) =
            all (\ n -> any ((n ==) . ind_num . ob_info) grp) [0..nums-1]
        check [] = error "MakeInvocations: check (impossible)"

        results :: [(Property eq,InvokeResult)]
        results =

            [
                let proofs :: [[Obligation eq Result]]
                    proofs
                        = filter check
                        $ groupSortedOn (ind_coords . ob_info)
                                [ ob | ob@Obligation{..} <- result
                                     , prop == ob_prop
                                     , success (snd $ ob_content)
                                ]

                in  (,) prop $ case proofs of
                        [] -> NoProof
                        grp:_ -> case grp of
                            [] -> error "MakeInvocations: results (impossible)"
                            Obligation _ (Induction [] _ _) _:_
                                -> ByPlain lemmas_used provers_used
                            Obligation _ (Induction cs _ _) _:_
                                -> ByInduction lemmas_used provers_used vars
                              where vars = varsFromCoords prop cs
                          where
                            provers_used = nub $ map (fst . ob_content) grp
                            lemmas_used  = fmap (nub . concat)
                                    $ sequence
                                    $ map (successLemmas . snd . ob_content) grp

            | prop <- props
            ]

    -- print results

    forM_ result $ \ Obligation{..} ->
        when (unknown (snd $ ob_content)) $ liftIO $ do
            putStrLn $ "Unknown from " ++ show (fst $ ob_content)
                ++ " on " ++ show ob_prop
                ++ ":" ++ show (snd $ ob_content)

    forM_ results $ \ (prop,invres) -> do

        writeInvRes (propName prop) invres

    return results

writeInvRes :: String -> InvokeResult -> HS ()
writeInvRes prop_name res = case res of
    ByInduction lemmas provers vars -> writeMsg $ InductiveProof prop_name lemmas (map show provers) vars
    ByPlain lemmas provers          -> writeMsg $ InductiveProof prop_name lemmas (map show provers) []
    NoProof                         -> writeMsg $ FailedProof prop_name

{-
parLoop :: [Property eq] -> [Property eq] -> HS ([Property eq],[Property eq])
parLoop props lemmas = do

    params <- getParams

    (proved,without_induction,unproved) <-
         partitionInvRes <$> tryProve props lemmas

    unless (null without_induction) $ liftIO $
         putStrLn $ unwords (map (showProperty True) without_induction)
                 ++ " provable without induction"

    if null proved || isolate params

         then return (unproved,lemmas++proved++without_induction)

         else do liftIO $ putStrLn $ "Adding " ++ show (length proved)
                         ++ " lemmas: " ++ intercalate ", " (map propName proved)
                 parLoop unproved
                         (lemmas ++ proved ++ without_induction)
                         -}

{-
showProperty :: Bool -> Property eq -> String
showProperty proved Property{..}
    | propOops && proved     = bold (colour Red propName)
    | propOops && not proved = colour Green propName
    | otherwise              = propName

printInfo :: forall eq . [Property eq] -> [Property eq] -> HS ()
printInfo unproved proved = liftIO $ do

    putStrLn ("Proved: "   ++ pr True proved)
    putStrLn ("Unproved: " ++ pr False unproved)
    putStrLn (show (len proved) ++ "/" ++ show (len (proved ++ unproved)))

    unless (null mistakes) $ putStrLn $ bold $ colour Red $
        "Proved " ++ show (length mistakes) ++ " oops: " ++ pr True mistakes

  where
    pr b xs | null xs   = "(none)"
            | otherwise = intercalate "\n\t" (map (showProperty b) xs)

    len :: [Property eq] -> Int
    len = length . filter (not . propOops)

    mistakes = filter propOops proved

-}
