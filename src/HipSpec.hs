{-# LANGUAGE RecordWildCards,PatternGuards,ViewPatterns #-}
module HipSpec (hipSpec, module Test.QuickSpec, fileName) where

import Test.QuickSpec
import Test.QuickSpec.Term hiding (depth)
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Main
import Test.QuickSpec.Equation
import Test.QuickSpec.Generate
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning(
  Context, (=:=), (=?=), unify, unifiable, execEQ, evalEQ, initial)

import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.QSTerm
import HipSpec.Init
import HipSpec.MakeInvocations
import HipSpec.Messages

import HipSpec.Params

import Halo.Monad
import Halo.Util
import Halo.Subtheory
import Halo.FOL.RemoveMin

import Data.List
import Data.Ord
import Data.Tuple
import Data.Function
import Data.Maybe
import qualified Data.Map as M

import Control.Monad
import Control.Monad.State

import System.Console.CmdArgs hiding (summary)
import Language.Haskell.TH

import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B

import System.IO
import Text.Printf

-- | Get up to n elements satisfying the predicate, those skipped, and the rest
--   (satisfies p,does not satisfy p (at most n),the rest)
getUpTo :: Int -> (a -> [a] -> Bool) -> [a] -> [a] -> ([a],[a],[a])
getUpTo 0 _ xs     _  = ([],[],xs)
getUpTo _ _ []     _  = ([],[],[])
getUpTo n p (x:xs) ys
   | p x ys    = let (s,u,r) = getUpTo n     p xs (x:ys) in (x:s,  u,r)
   | otherwise = let (s,u,r) = getUpTo (n-1) p xs (x:ys) in (  s,x:u,r)


-- | The main loop
deep :: HaloEnv                    -- ^ Environment to run HaltM
     -> Params                     -- ^ Parameters to the program
     -> (Msg -> IO ())             -- ^ Writer function
     -> Theory                     -- ^ Translated theory
     -> Sig                        -- ^ Configuration to QuickSpec
     -> [Tagged Term]              -- ^ The universe from QuickSpec
     -> [Prop]                     -- ^ The equations from QuickSpec
     -> IO ([Prop],[Prop],Context) -- ^ Resulting theorems and unproved
deep halt_env params@Params{..} write theory sig univ init_eqs =
    loop (initial (maxDepth sig) univ) init_eqs [] [] False
  where
    showEqs = map (showEquation sig . propQSTerms)

    loop :: Context                    -- ^ Prune state, to handle the congurece closure
         -> [Prop]                     -- ^ Equations to process
         -> [Prop]                     -- ^ Equations processed, but failed
         -> [Prop]                     -- ^ Equations proved
         -> Bool                       -- ^ Managed to prove something this round
         -> IO ([Prop],[Prop],Context) -- ^ Resulting theorems and unproved
    loop ctx []  failed proved False = return (proved,failed,ctx)
    loop ctx  []  failed proved True  = do putStrLn "Loop!"
                                           loop ctx failed [] proved False
    loop ctx eqs failed proved retry = do

      let discard :: Prop -> [Prop] -> Bool
          discard eq = \failedacc ->
                            any (isomorphicTo (propQSTerms eq))
                                (map propQSTerms failedacc)
                         || evalEQ ctx (unifiable (propQSTerms eq))

          (renamings,try,next) = getUpTo batchsize discard eqs failed

      unless (null renamings) $ do

        let shown = showEqs renamings

        write $ Discard shown

        putStrLn $
          let n = length renamings
          in if (n > 4)
                then "Discarding " ++ show n ++ " renamings and subsumptions."
                else "Discarding renamings and subsumptions: " ++ csv shown

      res <- tryProve halt_env params write try theory proved

      let (successes,without_induction,failures) = partitionInvRes res
          prunable = successes ++ without_induction

      if null prunable
          then loop ctx next (failed ++ failures) proved retry
          else do
              let ctx' :: Context
                  ctx' = execEQ ctx (mapM_ (unify . propQSTerms) prunable)

                  failed' :: [Prop]
                  failed' = failed ++ failures

                  -- Interesting candidates
                  (cand,failed_wo_cand)
                      = first (nubSortedOn propQSTerms . concat)
                      $ flip runState failed'
                      $ forM prunable
                      $ \prop -> do
                           failed <- get
                           let (cand,failed') = instancesOf ctx prop failed
                           put failed'
                           return cand

              if interesting_cands
                  then do
                      unless (null cand) $ do
                        let shown = showEqs cand
                        write $ Candidates $ shown
                        putStrLn $ "Interesting candidates: " ++ csv shown
                      loop ctx' (cand ++ next) failed_wo_cand
                               (proved ++ successes) True

                  else loop ctx' next failed' (proved ++ successes) True


    -- Renaming
    isomorphicTo :: Equation -> Equation -> Bool
    e1 `isomorphicTo` e2 =
      case matchEqSkeleton e1 e2 of
        Nothing -> False
        Just xs -> function xs && function (map swap xs)

    matchEqSkeleton :: Equation -> Equation -> Maybe [(Symbol, Symbol)]
    matchEqSkeleton (t :=: u) (t' :=: u') =
      liftM2 (++) (matchSkeleton t t') (matchSkeleton u u')

    matchSkeleton :: Term -> Term -> Maybe [(Symbol, Symbol)]
    matchSkeleton (T.Const f) (T.Const g) | f == g = return []
    matchSkeleton (T.Var x) (T.Var y) = return [(x, y)]
    matchSkeleton (T.App t u) (T.App t' u') =
      liftM2 (++) (matchSkeleton t t') (matchSkeleton u u')
    matchSkeleton _ _ = Nothing

    -- Relation is a function
    function :: (Ord a, Eq b) => [(a, b)] -> Bool
    function = all singleton . groupBy ((==) `on` fst) . nub . sortBy (comparing fst)
      where singleton xs = length xs == 1

    -- For interesting candidates
    instancesOf :: Context -> Prop -> [Prop] -> ([Prop],[Prop])
    instancesOf ctx new = partition (instanceOf ctx new)

    instanceOf :: Context -> Prop -> Prop -> Bool
    instanceOf ctx (propQSTerms -> new) (propQSTerms -> cand) =
      evalEQ ctx (new --> cand)
      where
        (t :=: u) --> (v :=: w) = do
          v =:= w
          t =?= u

-- Associativity is too good to overlook! -------------------------------------

-- If term is a function applied to two terms, Just return them
unbin :: Term -> Maybe (Symbol,Term,Term)
unbin (App (App (Const f) x) y) = Just (f,x,y)
unbin _ = Nothing

-- True if equation is an associativity equation
eqIsAssoc :: Equation -> Bool
eqIsAssoc
    ((unbin -> Just (f0,Var x0,unbin -> Just (g0,Var y0,Var z0)))
     :=:
     (unbin -> Just (f1,unbin -> Just (g1,Var x1,Var y1),Var z1)))
  = and [ f0 == f1 , g0 == g1 , f0 == g0
        , x0 == x1 , y0 == y1 , z0 == z1
        , x0 /= y0 , y0 /= z0 ]
eqIsAssoc _ = False

-- Main library ---------------------------------------------------------------

fileName :: ExpQ
fileName = location >>= \(Loc f _ _ _ _) -> stringE f

hipSpec :: Signature a => FilePath -> a -> IO ()
hipSpec file sig0 = do

    (write0, read) <- mkWriter

    write0 Started

    let sig = signature sig0
    (theory,halt_env,props,str_marsh,params@Params{..}) <- processFile file

    let write = if isJust json then write0 else const (return ())

    write FileProcessed

    when definitions $ do

        let getFunction s = case s of
                Subtheory (Function v) _ _ _ ->
                    let Subtheory _ _ _ fs = removeMinsSubthy s
                    in  Just (v,fs)
                _ -> Nothing

            func_map = M.fromList (mapMaybe getFunction (subthys theory))

            lookup_func x = fromMaybe [] (M.lookup x func_map)

            def_eqs = definitionalEquations str_marsh lookup_func sig

        putStrLn "\nDefinitional equations:"
        forM_ (zip [1 :: Int ..] def_eqs) $ \(i, eq) ->
            printf "%3d: %s\n" i (showEquation sig eq)

    classes <- fmap eraseClasses (generate sig)

    let eq_order eq = (assoc_important && not (eqIsAssoc eq), eq)
        swapEq (t :=: u) = u :=: t

        classToEqs :: [[Tagged Term]] -> [Equation]
        classToEqs = sortBy (comparing (eq_order . (swap_repr ? swapEq)))
                   . if quadratic
                          then sort . map (uncurry (:=:)) .
                               concatMap (uniqueCartesian . map erase)
                          else equations

        univ      = concat classes
        reps      = map (erase . head) classes
        prunedEqs = prune (maxDepth sig) univ reps (equations classes)
        eqs       = prepend_pruned ? (prunedEqs ++) $ classToEqs classes

        qsprops   = map (eqToProp str_marsh) eqs

        showEqs   = map (showEquation sig . propQSTerms)

    when quickspec $
         (writeFile (file++"_QuickSpecOutput.txt") ("All stuff from QuickSpec:\n" ++ intercalate "\n"
         (map show (classToEqs classes))))

    write $ QuickSpecDone (length classes) (length eqs)

    putStrLn "Starting to prove..."

    (qslemmas,qsunproved,ctx) <- deep halt_env params write theory sig univ qsprops

    when explore_theory $ do
      putStrLn "\nExplored theory (proved correct):"
      let provable (t :=: u) = evalEQ ctx (t =?= u)
          prunedEqs = prune (maxDepth sig) univ reps (filter provable (equations classes))
      forM_ (zip [1 :: Int ..] prunedEqs) $ \(i, eq) ->
        printf "%3d: %s\n" i (showEquation sig eq)

    write StartingUserLemmas

    (unproved,proved) <- parLoop halt_env params write theory props qslemmas

    write $ Finished
        (filter (`notElem` map propName qslemmas) $ map propName proved)
        (map propName unproved)
        (map propName qslemmas)
        (showEqs qsunproved)

    printInfo unproved proved

    unless dont_print_unproved $
        putStrLn $ "Unproved from QuickSpec: "
            ++ intercalate ", " (showEqs qsunproved)

    case json of
        Just json_file -> do
            msgs <- read
            B.writeFile json_file (encode msgs)
        Nothing -> return ()

