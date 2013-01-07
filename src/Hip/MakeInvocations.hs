{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
module Hip.MakeInvocations where

import Hip.ATP.Invoke
import Hip.ATP.Provers
import Hip.ATP.Results
import Hip.Params
import Hip.Trans.MakeProofs
import Hip.Trans.ProofDatatypes (propMatter)
import Hip.Trans.Theory
import Hip.Trans.Property
import Hip.Trans.TypeGuards
import qualified Hip.Trans.ProofDatatypes as PD

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

partitionInvRes :: [(a,InvokeResult)] -> ([a],[a],[a])
partitionInvRes []          = ([],[],[])
partitionInvRes ((x,ir):xs) = case ir of
    ByInduction{} -> (x:a,b,c)
    ByPlain{}     -> (a,x:b,c)
    NoProof       -> (a,b,x:c)
  where (a,b,c) = partitionInvRes xs

-- | Try to prove some properties in a theory, given some lemmas
tryProve :: HaloEnv -> Params -> [Prop] -> Theory -> [Prop]
         -> IO [(Prop,InvokeResult)]
tryProve halo_env params@(Params{..}) props thy lemmas = do
    let env = Env { reproveTheorems = False
                  , timeout         = timeout
                  , store           = output
                  , provers         = proversFromString provers
                  , processes       = processes
                  , propStatuses    = error "main env propStatuses"
                  , propCodes       = error "main env propCodes"
                  , z_encode        = z_encode_filenames
                  }

    us <- mkSplitUniqSupply 'c'

    let ((properties,_msgs),_us) = runMakerM halo_env us
                                 . mapM (\prop -> theoryToInvocations
                                                      params thy prop lemmas)
                                 $ props

        style_conf = StyleConf
             { style_comments   = comments
             , style_cnf        = not fof
             , style_dollar_min = False
             }

        toTPTP :: [Clause'] -> [HipSpecSubtheory] -> String
        toTPTP extra_clauses
            = (if readable_tptp then linStrStyleTPTP style_conf . fst . renameClauses
                    else dumpTPTP)
            . map (clauseMapFormula typeGuardFormula)
            . (not min ? removeMins)
            . (++ extra_clauses)
            . concatMap toClauses

        properties' =
            [ PD.Property n c $
              [ let lemma_deps =
                        [ lem | (provides -> lem@(Specific Lemma{})) <- subtheories ]
                    subs = trim subtheories (deps ++ lemma_deps)
                    pcls' = [ fmap (`toTPTP` subs) pcl | pcl <- pcls ]
                in  PD.Part m pcls'
              | PD.Part m (deps,subtheories,pcls) <- parts
              ]
            | PD.Property n c parts <- properties
            ]

    res <- invokeATPs properties' env

    forM res $ \property -> do

        let prop_name = PD.propName property
            invRes    = toInvokeResult property

        -- Need to figure out which of the input properties this
        -- invocation result corresponds to.
        -- This could obviously be done in a more elegant way.
        let err = error $ "Hip.ATP.MakeInvocations.tryProve: lost " ++ prop_name
            original = fromMaybe err $ find (\p -> prop_name == propName p) props

        let green | propOops original = Red
                  | otherwise         = Green

        putStrLn $ viewInvRes green prop_name invRes

        return (original,invRes)

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

parLoop :: HaloEnv -> Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
parLoop halo_env params thy props lemmas = do

    (proved,without_induction,unproved) <-
         partitionInvRes <$> tryProve halo_env params props thy lemmas

    unless (null without_induction) $
         putStrLn $ unwords (map (showProp True) without_induction)
                 ++ " provable without induction"

    if null proved || isolate params

         then return (unproved,lemmas++proved++without_induction)

         else do putStrLn $ "Adding " ++ show (length proved)
                         ++ " lemmas: " ++ intercalate ", " (map propName proved)
                 parLoop halo_env params thy unproved
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
