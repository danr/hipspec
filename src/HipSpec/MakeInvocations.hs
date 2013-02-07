{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
module HipSpec.MakeInvocations where

import HipSpec.ATP.Invoke
import HipSpec.ATP.Provers
import HipSpec.ATP.Results
import HipSpec.Params
import HipSpec.Trans.MakeProofs
import HipSpec.Trans.ProofDatatypes
import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.TypeGuards
import HipSpec.Messages
import qualified HipSpec.Trans.ProofDatatypes as PD

import Control.Concurrent.STM.Promise.Tree

import Halo.Monad
import Halo.Subtheory
import Halo.Trim
import Halo.Util

import Halo.FOL.Abstract
import Halo.FOL.Dump
import Halo.FOL.Linearise
import Halo.FOL.Operations
import Halo.FOL.RemoveMin
import Halo.FOL.Rename

import Data.List
import Data.Maybe

import Control.Monad

import UniqSupply

{-
data InvokeResult
    = ByInduction { invokeLemmas :: Maybe [String] }
    | ByPlain     { invokeLemmas :: Maybe [String] }
    | NoProof
  deriving (Eq,Ord,Show)

toInvokeResult :: PropResult -> InvokeResult
toInvokeResult p
    | Right lemmas <- plainProof p    = ByPlain lemmas
    | let status = fst (propMatter p)
    , status /= None                  = ByInduction (statusLemmas status)
    | otherwise                       = NoProof
    -}

-- We never put anything in the middle (by plain)
partitionInvRes :: [(a,Bool)] -> ([a],[a],[a])
partitionInvRes []          = ([],[],[])
partitionInvRes ((x,ir):xs) = case ir of
    True  -> (x:a,b,c)
    False -> (a,b,x:c)
  where (a,b,c) = partitionInvRes xs

-- | Try to prove some properties in a theory, given some lemmas
tryProve :: HaloEnv -> Params -> (Msg -> IO ()) -> [Prop] -> Theory -> [Prop]
         -> IO [(Prop,Bool)]
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

        trimmer :: [HipSpecContent] -> [HipSpecSubtheory]
        trimmer = trim (subthys ++ lemma_theories)

        handle :: HipSpecSubtheory -> String
        handle conj = toTPTP $ conj : lemma_theories ++ trimmer (calc_dependencies conj)

        proof_tree_tptp :: Tree (Property String)
        proof_tree_tptp = fmap (fmap handle) proof_tree

    let env = Env
            { timeout         = timeout
            , store           = output
            , provers         = proversFromString provers
            , processes       = processes
            , z_encode        = z_encode_filenames
            }

    proved <- invokeATPs proof_tree_tptp env

    let result = [ (p,any ((p ==) . prop_prop) proved) | p <- props ]

    forM_ result $ \ (prop,proved) -> do

        case proved of
            True -> do
                write $ Proved (propName prop)
                putStrLn $ "Proved " ++ propName prop ++ "!"
            False -> do
                write $ FailedProof (propName prop)
                putStrLn $ "Failed to prove " ++ propName prop

    return result

{-
writeInvRes write prop_name res = case res of
    ByInduction lemmas  -> write $ InductiveProof prop_name (view_lemmas lemmas)
    ByPlain lemmas      -> write $ PlainProof prop_name (view_lemmas lemmas)
    NoProof             -> write $ FailedProof prop_name
  where
    view_lemmas = fromMaybe []

viewInvRes green prop_name res = case res of
    ByInduction lemmas ->
        bold_green ("Proved " ++ prop_name) ++ view_lemmas lemmas
    ByPlain lemmas ->
        colour green ("Proved " ++ prop_name ++ " without induction")
         ++ view_lemmas lemmas
    NoProof -> "Failed to prove " ++ prop_name
  where
    bold_green = bold . colour green

    view_lemmas mx = case mx of
        Nothing  -> ""
        Just []  -> ", using no lemmas"
        Just [x] -> ", using " ++ x
        Just xs  -> ", using: " ++ concatMap ("\n\t" ++) xs ++ "\n"
        -}

parLoop :: HaloEnv -> Params -> (Msg -> IO ()) -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
parLoop halo_env params write thy props lemmas = do

    (proved,without_induction,unproved) <-
         partitionInvRes <$> tryProve halo_env params write props thy lemmas

    unless (null without_induction) $
         putStrLn $ unwords (map (showProp True) without_induction)
                 ++ " provable without induction"

    if null proved || isolate params

         then return (unproved,lemmas++proved++without_induction)

         else do putStrLn $ "Adding " ++ show (length proved)
                         ++ " lemmas: " ++ intercalate ", " (map propName proved)
                 parLoop halo_env params write thy unproved
                         (lemmas ++ proved ++ without_induction)

showProp :: Bool -> Prop -> String
showProp proved Prop{..}
    | propOops && proved     = bold (colour Red propName)
    | propOops && not proved = colour Green propName
    | otherwise              = propName

printInfo :: [Prop] -> [Prop] -> IO ()
printInfo unproved proved = do

    let pr b xs | null xs   = "(none)"
                | otherwise = intercalate "\n\t" (map (showProp b) xs)

        len :: [Prop] -> Int
        len = length . filter (not . propOops)

        mistakes = filter propOops proved

    putStrLn ("Proved: "   ++ pr True proved)
    putStrLn ("Unproved: " ++ pr False unproved)
    putStrLn (show (len proved) ++ "/" ++ show (len (proved ++ unproved)))

    unless (null mistakes) $ putStrLn $ bold $ colour Red $
        "Proved " ++ show (length mistakes) ++ " oops: " ++ pr True mistakes

