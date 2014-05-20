{-# LANGUAGE RecordWildCards, NamedFieldPuns, DoAndIfThenElse, ViewPatterns, CPP, PatternGuards #-}
module Main where

import Test.QuickSpec.Main (prune)
import Test.QuickSpec.Term (totalGen,Term,Expr,term,funs, Symbol,name)
import qualified Test.QuickSpec.Term as Term
import qualified Test.QuickSpec.Signature as Sig
import Test.QuickSpec.Equation (Equation(..), equations, TypedEquation(..), eraseEquation)
import Test.QuickSpec.Generate
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
-- import Test.QuickSpec.TestTotality
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import qualified Test.QuickSpec.TestTree as TestTree

import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as NER
-- import qualified Test.QuickSpec.Reasoning.PartialEquationalReasoning as PER

import HipSpec.Reasoning

import Data.Void

import HipSpec.Params (SuccessOpt(..))

import HipSpec.ThmLib
import HipSpec.Property hiding (Literal(..))
import HipSpec.Sig.QSTerm
import HipSpec.Init
import HipSpec.Monad hiding (equations)
import HipSpec.MainLoop

import HipSpec.Heuristics.Associativity
import HipSpec.Heuristics.CallGraph
import HipSpec.Utils

import HipSpec.Sig.Definitions

import Prelude hiding (read)

import qualified Data.Map as M

import Data.List
import Data.Maybe
import Data.Ord
import Data.Function

import Control.Monad

#ifdef SUPPORT_JSON
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B
#endif

import System.Exit (exitSuccess,exitFailure)

main :: IO ()
main = processFile $ \ m_sig_info user_props -> do
    writeMsg FileProcessed

    exit_act <- case m_sig_info of

        Nothing -> snd <$> runMainLoop NoCC user_props []

        Just (sig_info@SigInfo{..}) -> do

            (eqs,reps,classes) <- runQuickSpec sig_info

            Params{explore_theory,user_stated_first} <- getParams

            let (~+) | user_stated_first = flip (++)
                     | otherwise         = (++)

{-
            if bottoms then do

                let qsconjs = map (some (peqToProp sig_info)) eqs

                (ctx_init,tot_thms,tot_conjs) <- proveTotality sig_info reps

                ctx_with_def <- pruneWithDefEqs sig_info ctx_init

                void $ runMainLoop
                        ctx_with_def
                        (qsconjs ~+ map vacuous user_props ++ map vacuous tot_conjs)
                        (map vacuous tot_thms)

            else do
                        -}

            let qsconjs =
                    [ (etaExpandProp . generaliseProp . eqToProp sig_info i) eq
                    | (eq0,i) <- zip eqs [0..]
                    , let eq = some eraseEquation eq0
                    ]
            mapM_ (checkLint . lintProperty) qsconjs

            debugWhen PrintProps $ "\nQuickSpec Properties:\n" ++
                unlines (map show qsconjs)

            let ctx_init = NER.initial (maxDepth sig) (symbols sig) reps

            Env{theory} <- getEnv

            let def_eqs = definitions theory symbol_map

                ctx_with_def = execEQR ctx_init (mapM_ unify def_eqs)

            debugWhen PrintDefinitions $ "\nDefinitions as QuickSpec Equations:\n" ++
                unlines (map show def_eqs)

            (ctx_final,exit_act) <- runMainLoop ctx_with_def
                                     (qsconjs ~+ map vacuous user_props)
                                     []

            when explore_theory $ do
                let pruner   = prune ctx_init (map erase reps) id
                    provable = evalEQR ctx_final . equal
                    explored_theory
                        = filter (not . evalEQR ctx_with_def . equal)
                        $ pruner $ filter provable
                        $ map (some eraseEquation) (equations classes)
                writeMsg $ ExploredTheory $ map (showEquation sig) explored_theory

            return exit_act

#ifdef SUPPORT_JSON
    Params{json} <- getParams

    case json of
        Just json_file -> do
            msgs <- getMsgs
            liftIO $ B.writeFile json_file (encode msgs)
        Nothing -> return ()
#endif

    vacuous exit_act

runMainLoop :: EQR eq ctx cc => ctx -> [Property eq] -> [Theorem eq] -> HS (ctx,HS Void)
runMainLoop ctx_init initial_props initial_thms = do

    params@Params{only_user_stated,success,file} <- getParams

    whenFlag params QuickSpecOnly (liftIO exitSuccess)

    (theorems,conjectures,ctx_final) <- mainLoop ctx_init initial_props initial_thms

    let showProperties ps = [ (prop_name p,maybePropRepr p) | p <- ps ]
        theorems' = map thm_prop
                  . filter (\ t -> not (definitionalTheorem t) || isUserStated (thm_prop t))
                  $ theorems
        notQS  = filter (not . isFromQS)
        fromQS = filter isFromQS

    writeMsg Finished
        { proved      = showProperties $ notQS theorems'
        , unproved    = showProperties $ notQS conjectures
        , qs_proved   = showProperties $ fromQS theorems'
        , qs_unproved =
            if only_user_stated then [] else showProperties $ fromQS conjectures
        }

    let exit_act = liftIO $ case success of
            NothingUnproved -> do
                putStr (file ++ ", " ++ show success ++ ":")
                if null conjectures
                    then putStrLn "ok" >> exitSuccess
                    else putStrLn "fail" >> exitFailure
            ProvesUserStated -> do
                putStr (show success ++ ":")
                if null (notQS conjectures)
                    then putStrLn "ok" >> exitSuccess
                    else putStrLn "fail" >> exitFailure
            CleanRun -> exitSuccess

    return (ctx_final,exit_act)

runQuickSpec :: SigInfo -> HS ([Some TypedEquation],[Tagged Term],[Several Expr])
runQuickSpec SigInfo{..} = do

    Params{..} <- getParams

    let callg = transitiveCallGraph resolve_map

    debugWhen PrintCallGraph $ "\nCall Graph:\n" ++ unlines
        [ show s ++ " calls " ++ show ss
        | (s,ss) <- M.toList callg
        ]

    r <- liftIO $ generate isabelle_mode (const totalGen) sig
                        -- shut up if we're on isabelle mode

    let classes = concatMap (some2 (map (Some . O) . TestTree.classes)) (TypeMap.toList r)
        eq_order eq = (assoc_important && not (eqIsAssoc eq), eq)
        swapEq (t :=: u) = u :=: t

        equation_funs :: Some TypedEquation -> [Symbol]
        equation_funs (some eraseEquation -> t1 :=: t2)
            = funs t1 `union` funs t2

        equations' :: [Several Expr] -> [Some TypedEquation]
        equations' = concatMap (several (map Some . toEquations))

        term_calls :: Expr a -> [Symbol]
        term_calls e
            = nubSorted
            . concat
            . mapMaybe (`M.lookup` callg)
            . funs . term $ e

        eq_calls :: TypedEquation a -> [Symbol]
        eq_calls (e1 :==: e2) = nubSorted (term_calls e1 ++ term_calls e2)

        toEquations :: [Expr a] -> [TypedEquation a]
        toEquations es@(x:xs)
            | call_graph = [ toEquation y (reverse ys)
                           | y:ys <- tails (reverse es)
                           , not (null ys)
                           ]
            | otherwise = [ y :==: x | y <- xs ]
        toEquations [] = error "HipSpec.toEquations internal error"

        toEquation :: Expr a -> [Expr a] -> TypedEquation a
        toEquation e rcs = foldr1 best (map (e :==:) rcs)
          where
            best eq1 eq2
                | eq_calls eq1 == term_calls e             = eq1
                | eq_calls eq2 `isSupersetOf` eq_calls eq1 = eq1
                | otherwise                                = eq2

        classToEqs :: [Several Expr] -> [Some TypedEquation]
        classToEqs
            = concatMap
                (sortBy (comparing ( eq_order . (swap_repr ? swapEq)
                                   . some eraseEquation)
                                   )
                )
            . (if call_graph
                   then sortByGraph callg equation_funs
                   else (:[]))
            . if quadratic
                   then concatMap ( several (map (Some . uncurry (:==:))
                                  . uniqueCartesian)
                                  )
                   else equations'

        ctx_init  = NER.initial (maxDepth sig) (symbols sig) reps

        reps = map (some2 (tagged term . head)) classes

        pruner    = prune ctx_init (map erase reps) (some eraseEquation)
        prunedEqs = pruner (equations classes)
        eqs       = prepend_pruned ? (prunedEqs ++) $ classToEqs classes

    debugWhen PrintEqClasses $ "\nEquivalence classes:\n" ++ unlines
        (map (show . several (map term)) classes)

    writeMsg $ QuickSpecDone (length classes) (length eqs)

    when isabelle_mode $ do
        Env{theory} <- getEnv
        let def_eqs  = definitions theory symbol_map
            ctx_defs = execEQR ctx_init (mapM_ unify def_eqs)
--            pruner'  = prune ctx_init (map erase reps) (some eraseEquation)
        debugWhen PrintDefinitions $ "\nDefinitions as QuickSpec Equations:\n" ++
            unlines (map show def_eqs)
        liftIO $ do
            mapM_ putStrLn
                $ nub
                $ map isabelleShowPrecondition
                $ filter (\(pre, _) -> length pre == cond_count)
                $ concatMap isabelleFilterEquations
                $ groupBy ((==) `on` snd)
                $ sortBy (comparing snd)
                $ map (isabelleShowEquation cond_name sig)
      --          $ map show
                $ filter (not . evalEQR ctx_defs . equal)
                $ map (some eraseEquation) eqs -- prunedEqs
            exitSuccess

    return (eqs,reps,classes)

isabelleShowPrecondition :: ([String], String) -> String
isabelleShowPrecondition ([], xs) = xs
isabelleShowPrecondition (pre, xs) = intercalate " & " pre ++ " ==> " ++ xs

isabelleFilterEquations :: [([String], String)] -> [([String], String)]
isabelleFilterEquations xss@((_, xs):_)
  | ([], xs) `elem` xss = [([], xs)]
  | otherwise = xss

isabelleShowEquation :: String -> Sig -> Equation -> ([String], String)
isabelleShowEquation cond_nm sig (t :=: u) = (precondition, showTerm t' ++ " = " ++ showTerm u')
  where
    [t',u'] = map quoteTerm [t,u]

    quoteTerm = Term.mapVars f . Term.mapConsts (onName g)

    showTerm = show . Term.mapVars delBackquote

    backquoted = map delBackquote $ filter isBackquoted (nub (Term.vars t' ++ Term.vars u'))

    precondition = map (\x -> cond_nm ++ " " ++ name x) backquoted

    onName h s = s { Term.name = h (Term.name s) }

    f :: Symbol -> Symbol
    f x = backquotify x (Sig.disambiguate sig (Term.vars t ++ Term.vars u) x)

    isBackquoted :: Symbol -> Bool
    isBackquoted a = case name a of
        '`':_ -> True
        _     -> False

    backquotify :: Symbol -> Symbol -> Symbol
    backquotify a = if isBackquoted a then addBackquote else delBackquote

    delBackquote :: Symbol -> Symbol
    delBackquote a = case name a of
        '`':xs -> a { name = xs }
        _      -> a

    addBackquote :: Symbol -> Symbol
    addBackquote a = case name a of
        '`':_ -> a
        xs    -> a { name = '`':xs }

    g x =
      case lookup x isabelleFunctionNames of
        Nothing -> x
        Just y -> y

isabelleFunctionNames :: [(String, String)]
isabelleFunctionNames =
  [(":", "#"),
   ("++", "@"),
   ("reverse", "rev"),
   ("plus_nat", "Groups.plus_class.plus"),
   ("Zero_nat", "Groups.zero_class.zero"),
   ("one_nat", "Groups.one_class.one")]


{-

proveTotality :: SigInfo -> [Tagged Term] -> HS (PER.Context,[Theorem Void],[Property Void])
proveTotality SigInfo{..} univ = do

    tot_list <- liftIO $ testTotality sig

    let tot_props
            = [ tot_prop
              | (sym,totality) <- tot_list
              , Just v <- [maybeLookupSym resolve_map sym]
              , not (isDataConId v)
              , Just tot_prop <- [totalityProperty v totality]
              ]

    (proved_tot,unproved_tot,NoCC) <- mainLoop NoCC tot_props []

    let ctx_init = PER.initial (maxDepth sig) tot_list univ

    return (ctx_init,proved_tot,unproved_tot)
-}
