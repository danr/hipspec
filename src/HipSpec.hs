{-# LANGUAGE RecordWildCards,PatternGuards,ViewPatterns #-}
module HipSpec (hipSpec, module Test.QuickSpec, fileName) where

import Test.QuickSpec
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Equation
import Test.QuickSpec.Generate
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.TestTotality
import Test.QuickSpec.Reasoning.PartialEquationalReasoning
    ( execPEQ, evalPEQ, unify, equal
    , initial, Context
    , PEquation(..)
    , showPEquation )

import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.QSTerm
import HipSpec.Init
import HipSpec.MakeInvocations
import HipSpec.Messages hiding (equations)

import HipSpec.MainLoop

import HipSpec.Heuristics.Associativity

import HipSpec.Params

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

import Text.Printf


-- Main library ---------------------------------------------------------------

fileName :: ExpQ
fileName = location >>= \(Loc f _ _ _ _) -> stringE f

hipSpec :: Signature a => FilePath -> a -> IO ()
hipSpec file sig0 = do

    (write0, read) <- mkWriter

    write0 Started

    let sig = signature sig0 `mappend` withTests 100

        showEq :: PEquation -> String
        showEq = showPEquation sig

        showEqs :: [PEquation] -> [String]
        showEqs = map showEq

        showProperty :: Property -> String
        showProperty = showEq . propQSTerms

        showProperties :: [Property] -> [String]
        showProperties = map showProperty

        printNumberedEqs :: [PEquation] -> IO ()
        printNumberedEqs eqs = forM_ (zip [1 :: Int ..] eqs) $ \(i, eq) ->
            printf "%3d: %s\n" i (showEq eq)

    (theory,halo_env,props,str_marsh,params@Params{..}) <- processFile file

    let write = if isJust json then write0 else const (return ())

    write FileProcessed

    let getFunction s = case s of
            Subtheory (Function v) _ _ _ ->
                let Subtheory _ _ _ fs = removeMinsSubthy s
                in  Just (v,fs)
            _ -> Nothing

        func_map = M.fromList (mapMaybe getFunction (subthys theory))

        lookup_func x = fromMaybe [] (M.lookup x func_map)

        def_eqs = definitionalEquations str_marsh lookup_func sig

    when definitions $ do
        putStrLn "\nDefinitional equations:"
        printNumberedEqs def_eqs

    tot_list <- testTotality sig

    classes <- fmap eraseClasses (generate (const T.totalGen) sig)

    let eq_order eq = (assoc_important && not (eqIsAssoc eq), eq)
        swapEq (t :=: u) = u :=: t

        classToEqs :: [[Tagged T.Term]] -> [Equation]
        classToEqs
            = sortBy (comparing (eq_order . (swap_repr ? swapEq)))
            . if quadratic
                   then sort . map (uncurry (:=:)) .
                        concatMap (uniqueCartesian . map erase)
                   else equations

        ctx_init   = initial (maxDepth sig) tot_list univ
        univ       = map head classes
        reps       = map (erase . head) classes

        ctx0       = execPEQ ctx_init (mapM_ unify def_eqs)

        pruner     = pprune ctx0

        prunedEqs
            = map untotalise
            . pruner
            . map totalise
            . equations
            $ classes

        eqs        = prepend_pruned ? (prunedEqs ++) $ classToEqs classes


        definition = evalPEQ ctx0 . equal

        qsprops    = filter (not . definition . propQSTerms)
                   $ map (eqToProp str_marsh) eqs

        peqs       = map totalise eqs

    when quickspec $ writeFile (file ++ "_QuickSpecOutput.txt") $
        "All stuff from QuickSpec:\n" ++
        intercalate "\n" (map show (classToEqs classes))

    write $ QuickSpecDone (length classes) (length eqs)

    putStrLn "Starting to prove..."

    (qslemmas,qsunproved,ctx) <- deep halo_env params write theory showEq ctx0 qsprops

{-
    when explore_theory $ do
        let provable        = evalPEQ ctx . equal
            explored_theory = pruner $ filter provable (equations classes)
        write $ ExploredTheory (showEqs explored_theory)
        putStrLn "\nExplored theory (proved correct):"
        printNumberedEqs explored_theory
        -}

    write StartingUserLemmas

    (unproved,proved) <- parLoop halo_env params write theory props qslemmas

    write $ Finished
        (filter (`notElem` map propName qslemmas) $ map propName proved)
        (map propName unproved)
        (map propName qslemmas)
        (showProperties qsunproved)

    printInfo unproved proved

    unless dont_print_unproved $
        putStrLn $ "Unproved from QuickSpec: " ++ csv (showProperties qsunproved)

    case json of
        Just json_file -> do
            msgs <- read
            B.writeFile json_file (encode msgs)
        Nothing -> return ()

pprune :: Context -> [PEquation] -> [PEquation]
pprune ctx = evalPEQ ctx . filterM (fmap not . unify)

totalise :: Equation -> PEquation
totalise eq = [] :\/: eq

untotalise :: PEquation -> Equation
untotalise ([] :\/: eq) = eq

