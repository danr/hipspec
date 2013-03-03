{-# LANGUAGE RecordWildCards,NamedFieldPuns #-}
module HipSpec (hipSpec, module Test.QuickSpec, fileName) where

import Test.QuickSpec

import Test.QuickSpec.Main (prune)
import Test.QuickSpec.Term (totalGen,Term)
import Test.QuickSpec.Equation (Equation(..), equations)
import Test.QuickSpec.Generate
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.TestTotality

import Test.QuickSpec.Reasoning.PartialEquationalReasoning
    (PEquation(..), {- evalPEQ, -} showPEquation)

import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as NER
import qualified Test.QuickSpec.Reasoning.PartialEquationalReasoning as PER

import HipSpec.Reasoning
import HipSpec.Void

import HipSpec.Trans.Obligation
import HipSpec.Trans.Property
import HipSpec.Trans.QSTerm
import HipSpec.Init
import HipSpec.Monad hiding (equations)
import HipSpec.MainLoop
import HipSpec.Heuristics.Associativity
import HipSpec.Trans.DefinitionalEquations
import HipSpec.StringMarshal (maybeLookupSym)

import Prelude hiding (read)

import Halo.Util

import Data.List
import Data.Ord

import Control.Monad

import Language.Haskell.TH

import Data.Monoid (mappend)

import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B

fileName :: ExpQ
fileName = location >>= \(Loc f _ _ _ _) -> stringE f

hipSpec :: Signature a => FilePath -> a -> IO ()
hipSpec file sig0 = runHS (signature sig0 `mappend` withTests 100) $ do

    writeMsg Started

    processFile file $ \ user_props -> do

        writeMsg FileProcessed

        Info{str_marsh,sig} <- getInfo

        Params{bottoms,explore_theory} <- getParams

        (eqs,univ,reps,classes) <- runQuickSpec

        if bottoms then do

                let qsconjs = map (peqToProp (showPEquation sig) str_marsh)
                                  (map totalise eqs)

                (ctx_init,tot_thms,tot_conjs) <- proveTotality univ

                void $ runMainLoop
                        ctx_init
                        (qsconjs ++ map (fmap absurd) (tot_conjs ++ user_props))
                        (map (fmap absurd) tot_thms)

            else do

                let qsconjs = map (eqToProp (showEquation sig) str_marsh) eqs

                    ctx_init = NER.initial (maxDepth sig) (symbols sig) univ

                (ctx_with_def,ctx_final) <-
                    runMainLoop ctx_init
                                (qsconjs ++ map (fmap absurd) user_props)
                                []

                when explore_theory $ do
                    let pruner   = prune ctx_with_def reps
                        provable = evalEQR ctx_final . equal
                        explored_theory
                            = pruner $ filter provable (equations classes)
                    writeMsg $ ExploredTheory $
                        map (showEquation sig) explored_theory

        Params{json} <- getParams

        case json of
            Just json_file -> do
                msgs <- getMsgs
                liftIO $ B.writeFile json_file (encode msgs)
            Nothing -> return ()

runMainLoop :: (MakeEquation eq,EQR eq ctx cc)
            => ctx -> [Property eq] -> [Theorem eq] -> HS (ctx,ctx)
runMainLoop ctx_init initial_props initial_thms = do

    ctx_with_def <- pruneWithDefEqs ctx_init

    (theorems,conjectures,ctx_final) <-
        mainLoop ctx_with_def initial_props initial_thms

    let showProperties = map propName
        notQS  = filter (not . isFromQS)
        fromQS = filter isFromQS

    writeMsg $ Finished
        (showProperties $ notQS $ map thm_prop theorems)
        (showProperties $ notQS conjectures)
        (showProperties $ fromQS $ map thm_prop theorems)
        (showProperties $ fromQS conjectures)

    return (ctx_with_def,ctx_final)

runQuickSpec :: HS ([Equation],[Tagged Term],[Term],[[Tagged Term]])
runQuickSpec = do

    Info{..} <- getInfo
    let Params{..} = params

    classes <- liftIO $ fmap eraseClasses (generate (const totalGen) sig)

    let eq_order eq = (assoc_important && not (eqIsAssoc eq), eq)
        swapEq (t :=: u) = u :=: t

        classToEqs :: [[Tagged Term]] -> [Equation]
        classToEqs = sortBy (comparing (eq_order . (swap_repr ? swapEq)))
                   . if quadratic
                          then sort . map (uncurry (:=:)) .
                               concatMap (uniqueCartesian . map erase)
                          else equations

        univ      = map head classes
        ctx_init  = NER.initial (maxDepth sig) (symbols sig) univ

        reps      = map (erase . head) classes

        pruner    = prune ctx_init reps  -- this one or similar for explore theory
        prunedEqs = pruner (equations classes)
        eqs       = prepend_pruned ? (prunedEqs ++) $ classToEqs classes


    writeMsg $ QuickSpecDone (length classes) (length eqs)

    return (eqs,univ,reps,classes)

proveTotality :: [Tagged Term] -> HS (PER.Context,[Theorem Void],[Property Void])
proveTotality univ = do

    Info{..} <- getInfo

    tot_list <- liftIO $ testTotality sig

    let tot_props
            = [ tot_prop
              | (sym,totality) <- tot_list
              , Just (v,True) <- [maybeLookupSym str_marsh sym]
              , Just tot_prop <- [totalityProperty v totality]
              ]

    (proved_tot,unproved_tot,NoCC) <- mainLoop NoCC tot_props []

    let ctx_init = PER.initial (maxDepth sig) tot_list univ

    return (ctx_init,proved_tot,unproved_tot)

totalise :: Equation -> PEquation
totalise eq = [] :\/: eq

