{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
module HipSpec.MakeInvocations where

import HipSpec.ATP.Invoke
import HipSpec.ATP.Provers
import HipSpec.ATP.Results
import HipSpec.Params
import HipSpec.Trans.MakeProofs
import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.TypeGuards
import HipSpec.Messages

import Control.Concurrent.STM.Promise.Tree

import Halo.Monad
import Halo.Subtheory
import Halo.Trim
import Halo.Util
import Halo.Shared

import Halo.FOL.Abstract
import Halo.FOL.Dump
import Halo.FOL.Linearise
import Halo.FOL.Operations
import Halo.FOL.RemoveMin
import Halo.FOL.Rename

import Data.List
import Data.Maybe
import Data.Monoid

import Control.Monad

import UniqSupply

import Var

data InvokeResult
    = ByInduction { invoke_lemmas :: Maybe [String], provers :: [ProverName], vars :: [String] }
    | ByPlain     { invoke_lemmas :: Maybe [String], provers :: [ProverName] }
    | NoProof
  deriving (Eq,Ord)

partitionInvRes :: [(a,InvokeResult)] -> ([a],[a],[a])
partitionInvRes []          = ([],[],[])
partitionInvRes ((x,ir):xs) = case ir of
    ByInduction{} -> (x:a,b,c)
    ByPlain{}     -> (a,x:b,c)
    NoProof{}     -> (a,b,x:c)
  where (a,b,c) = partitionInvRes xs

-- | Try to prove some properties in a theory, given some lemmas
tryProve :: HaloEnv -> Params -> (Msg -> IO ()) -> [Property] -> Theory -> [Property]
         -> IO [(Property,InvokeResult)]
tryProve _        _                   _     []    _          _      = return []
tryProve halo_env params@(Params{..}) write props Theory{..} lemmas = do

    us <- mkSplitUniqSupply 'c'

    let (lemma_theories,_) = runHaloM halo_env (mapM translateLemma lemmas)

        ((proof_tree,_),_) = runMakerM halo_env us $ (tryAll <$> mapM (makeProofs params) props)

        style_conf = StyleConf
             { style_comments   = comments
             , style_cnf        = not fof
             , style_dollar_min = False
             }

        toTPTP :: [HipSpecSubtheory] -> String
        toTPTP
            = (if readable_tptp then linStrStyleTPTP style_conf . fst . renameClauses
                    else dumpTPTP)
            . map (clauseMapFormula typeGuardFormula)
            . (not min ? removeMins)
            . concatMap toClauses

        calc_dependencies :: HipSpecSubtheory -> [HipSpecContent]
        calc_dependencies s = concatMap depends (s:lemma_theories)

        fetcher :: [HipSpecContent] -> [HipSpecSubtheory]
        fetcher = trim (subthys ++ lemma_theories)

        fetch_and_make_tptp :: HipSpecSubtheory -> String
        fetch_and_make_tptp conj = toTPTP $
            conj : lemma_theories ++ fetcher (calc_dependencies conj)

        proof_tree_tptp :: Tree (Obligation (Proof String))
        proof_tree_tptp = fmap (fmap (fmap fetch_and_make_tptp)) proof_tree

    let env = Env
            { timeout         = timeout
            , store           = output
            , provers         = proversFromString provers
            , processes       = processes
            , z_encode        = z_encode_filenames
            }

    result <- invokeATPs proof_tree_tptp env

    let results =

            [
                let proofs = groupSortedOn ind_coords
                                [ proof | Obligation prop' proof <- result
                                        , prop == prop'
                                        , success (snd $ proof_content proof)
                                ]

                    check grp@(Induction _ _ nums _:_) = all (\ n -> any ((n ==) . ind_num) grp) [0..nums-1]

                    proofs' = filter check proofs

                in  (,) prop $ case proofs' of
                        [] -> NoProof
                        grp:_ -> case grp of
                            Induction [] _ _ _:_ -> ByPlain lemmas provers
                            Induction cs _ _ _:_ -> ByInduction lemmas provers vars
                              where vars = varsFromCoords prop cs
                          where
                            provers = nub $ map (fst . proof_content) grp
                            lemmas  = fmap nub $ mconcat $ map (successLemmas . snd . proof_content) grp

            | prop <- props
            ]

    -- print result
    forM_ result $ \ (Obligation prop proof) -> when (failure (snd $ proof_content proof)) $ do
        putStrLn $ "Failure from " ++ show (fst $ proof_content proof)
            ++ " on " ++ show prop
            ++ ":" ++ show (snd $ proof_content proof)

    forM_ results $ \ (prop,invres) -> do

        writeInvRes write (propName prop) invres

        putStrLn $ viewInvRes Green (propName prop) invres

    return results

writeInvRes write prop_name res = case res of
    ByInduction lemmas provers vars -> write $ InductiveProof prop_name (view_lemmas lemmas)
    ByPlain lemmas provers          -> write $ PlainProof prop_name (view_lemmas lemmas)
    NoProof                         -> write $ FailedProof prop_name
  where
    view_lemmas = fromMaybe []

viewInvRes green prop_name res = case res of
    ByInduction lemmas provers vars ->
        bold_green ("Proved " ++ prop_name ++ " by induction on " ++ csv id vars)
            ++ view_provers provers ++ view_lemmas lemmas
    ByPlain lemmas provers ->
        colour green ("Proved " ++ prop_name ++ " without induction")
            ++ view_provers provers ++ view_lemmas lemmas
    NoProof -> "Failed to prove " ++ prop_name
  where
    bold_green = bold . colour green

    csv :: (a -> String) -> [a] -> String
    csv f = intercalate "," . map f

    view_provers ps = " using " ++ csv show ps

    view_lemmas mx = case mx of
        Nothing  -> ""
        Just []  -> ", using no lemmas"
        Just [x] -> ", using " ++ x
        Just xs  -> ", using: " ++ concatMap ("\n\t" ++) xs ++ "\n"

parLoop :: HaloEnv -> Params -> (Msg -> IO ()) -> Theory -> [Property] -> [Property] -> IO ([Property],[Property])
parLoop halo_env params write thy props lemmas = do

    (proved,without_induction,unproved) <-
         partitionInvRes <$> tryProve halo_env params write props thy lemmas

    unless (null without_induction) $
         putStrLn $ unwords (map (showProperty True) without_induction)
                 ++ " provable without induction"

    if null proved || isolate params

         then return (unproved,lemmas++proved++without_induction)

         else do putStrLn $ "Adding " ++ show (length proved)
                         ++ " lemmas: " ++ intercalate ", " (map propName proved)
                 parLoop halo_env params write thy unproved
                         (lemmas ++ proved ++ without_induction)

showProperty :: Bool -> Property -> String
showProperty proved Property{..}
    | propOops && proved     = bold (colour Red propName)
    | propOops && not proved = colour Green propName
    | otherwise              = propName

printInfo :: [Property] -> [Property] -> IO ()
printInfo unproved proved = do

    let pr b xs | null xs   = "(none)"
                | otherwise = intercalate "\n\t" (map (showProperty b) xs)

        len :: [Property] -> Int
        len = length . filter (not . propOops)

        mistakes = filter propOops proved

    putStrLn ("Proved: "   ++ pr True proved)
    putStrLn ("Unproved: " ++ pr False unproved)
    putStrLn (show (len proved) ++ "/" ++ show (len (proved ++ unproved)))

    unless (null mistakes) $ putStrLn $ bold $ colour Red $
        "Proved " ++ show (length mistakes) ++ " oops: " ++ pr True mistakes

