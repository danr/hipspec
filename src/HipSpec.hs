{-# LANGUAGE RecordWildCards #-}
module HipSpec (hipSpec, module Test.QuickSpec, fileName) where

import Test.QuickSpec

import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Equation (Equation(..), equations)
import Test.QuickSpec.Generate
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.TestTotality

{-
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning
    ()
    -}
import Test.QuickSpec.Reasoning.PartialEquationalReasoning
    (PEquation(..), evalPEQ, execPEQ, showPEquation)

{-
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as NER
-}
import qualified Test.QuickSpec.Reasoning.PartialEquationalReasoning as PER

import HipSpec.Reasoning

import HipSpec.StringMarshal
import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.QSTerm
import HipSpec.Init
import HipSpec.MakeInvocations
import HipSpec.Monad hiding (equations)
import HipSpec.MainLoop
import HipSpec.Heuristics.Associativity

import Prelude hiding (read)

import Halo.Util
import Halo.Subtheory
import Halo.FOL.RemoveMin

import Data.List
import Data.Ord
import Data.Maybe
import qualified Data.Map as M

import Control.Monad

import Language.Haskell.TH

import Data.Monoid (mappend)

import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B

{-
import Text.Printf
-}

-- Main library ---------------------------------------------------------------

fileName :: ExpQ
fileName = location >>= \(Loc f _ _ _ _) -> stringE f

hipSpec :: Signature a => FilePath -> a -> IO ()
hipSpec file sig0 = runHS $ do

    writeMsg Started

    let sig = signature sig0 `mappend` withTests 100

{-
        showEq :: PEquation -> String
        showEq = showPEquation sig

        showProperty :: Property -> String
        showProperty = propName


        printNumberedEqs :: [PEquation] -> IO ()
        printNumberedEqs eqs = forM_ (zip [1 :: Int ..] eqs) $ \(i, eq) ->
            printf "%3d: %s\n" i (showEq eq)
            -}

    processFile file $ \ (props,str_marsh) -> do

        theory <- getTheory
        Params{..} <- getParams

        writeMsg FileProcessed

        let getFunction s = case s of
                Subtheory (Function v) _ _ _ ->
                    let Subtheory _ _ _ fs = removeMinsSubthy s
                    in  Just (v,fs)
                _ -> Nothing

            func_map = M.fromList (mapMaybe getFunction (subthys theory))

            lookup_func x = fromMaybe [] (M.lookup x func_map)

            def_eqs = definitionalEquations str_marsh lookup_func sig

{-
        when definitions $ liftIO $ do
            putStrLn "\nDefinitional equations:"
            printNumberedEqs def_eqs
            -}

        abcde <- initialisePEQ sig str_marsh def_eqs
        uncurry4 (remaining props) abcde

remaining :: EQR eq ctx cc
          => [Property eq]
          -> ctx
          -> [Property eq]
          -> [Property eq]
          -> [Property eq]
          -> HS ()
remaining props ctx0 qsprops already_proved already_failures = do

    Params{..} <- getParams

    (qslemmas,qsunproved,_ctx) <- deep ctx0 qsprops already_proved

    writeMsg StartingUserLemmas

    (unproved,proved) <- parLoop props qslemmas

    let showProperties = map propName

    writeMsg $ Finished
        (filter (`notElem` map propName qslemmas) $ map propName proved)
        (map propName unproved)
        (map propName qslemmas)
        (showProperties qsunproved)

    printInfo (unproved ++ already_failures) proved

    unless dont_print_unproved $ liftIO $
        putStrLn $ "Unproved from QuickSpec: " ++ csv (showProperties qsunproved)

    case json of
        Just json_file -> do
            msgs <- getMsgs
            liftIO $ B.writeFile json_file (encode msgs)
        Nothing -> return ()

initialisePEQ :: Sig -> StrMarsh -> [PEquation]
              -> HS (PER.Context,[Property PEquation],[Property PEquation],[Property PEquation])
initialisePEQ sig str_marsh def_eqs = do

    Params{..} <- getParams

    tot_list <- liftIO $ testTotality sig

    let tot_props
            = [ tot_prop
              | (sym,totality) <- tot_list
              , Just (v,True) <- [maybeLookupSym str_marsh sym]
              , Just tot_prop <- [totalityProperty v totality]
              ]

    (unproved_tot,proved_tot) <- parLoop tot_props []

    classes <- liftIO $ fmap eraseClasses (generate (const T.totalGen) sig)

    let eq_order eq = (assoc_important && not (eqIsAssoc eq), eq)
        swapEq (t :=: u) = u :=: t

        classToEqs :: [[Tagged T.Term]] -> [Equation]
        classToEqs
            = sortBy (comparing (eq_order . (swap_repr ? swapEq)))
            . if quadratic
                   then sort . map (uncurry (:=:)) .
                        concatMap (uniqueCartesian . map erase)
                   else equations

        ctx_init   = PER.initial (maxDepth sig) tot_list univ
        univ       = map head classes

        ctx0       = execPEQ ctx_init (mapM_ unify def_eqs)

        pruner     = pprune ctx0

        prunedEqs
            = pruner
            . map totalise
            . equations
            $ classes

        eqs        = prepend_pruned ? (prunedEqs ++)
                   $ map totalise (classToEqs classes)

        qsprops    = filter (not . is_def)
                   $ map (peqToProp (showPEquation sig) str_marsh) eqs
          where
            definition = evalPEQ ctx0 . equal

            is_def p = case propEquation p of
                Just eq -> definition eq
                _       -> False

    return (ctx0,qsprops,proved_tot,unproved_tot)

pprune :: PER.Context -> [PEquation] -> [PEquation]
pprune ctx = evalPEQ ctx . filterM (fmap not . PER.unify)

totalise :: Equation -> PEquation
totalise eq = [] :\/: eq

{-
untotalise :: PEquation -> Equation
untotalise ([] :\/: eq) = eq
untotalise _ = error "Untotalize on a non-total PEquation"
-}

uncurry4 :: (a -> b -> c -> d -> e) -> ((a,b,c,d) -> e)
uncurry4 f (a,b,c,d) = f a b c d
