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

import HipSpec.Params

import Halo.Monad
import Halo.Util

import Data.List
import Data.Ord
import Data.Tuple
import Data.Function

import Control.Monad
import Control.Monad.State

import System.Console.CmdArgs hiding (summary)
import Language.Haskell.TH

import System.IO

-- | Get up to n elements satisfying the predicate, those skipped, and the rest
--   (satisfies p,does not satisfy p (at most n),the rest)
getUpTo :: Int -> (a -> [a] -> Bool) -> [a] -> [a] -> ([a],[a],[a])
getUpTo 0 _ xs     _  = ([],[],xs)
getUpTo _ _ []     _  = ([],[],[])
getUpTo n p (x:xs) ys
   | p x ys    = let (s,u,r) = getUpTo n     p xs (x:ys) in (x:s,  u,r)
   | otherwise = let (s,u,r) = getUpTo (n-1) p xs (x:ys) in (  s,x:u,r)

-- | The main loop
deep :: HaloEnv            -- ^ Environment to run HaltM
     -> Params             -- ^ Parameters to the program
     -> Theory             -- ^ Translated theory
     -> Sig                -- ^ Configuration to QuickSpec
     -> [Tagged Term]      -- ^ The universe from QuickSpec
     -> [Prop]             -- ^ The equations from QuickSpec
     -> IO ([Prop],[Prop]) -- ^ Resulting theorems and unproved
deep halt_env params@Params{..} theory sig univ init_eqs =
    loop (initial (maxDepth sig) univ) init_eqs [] [] False
  where
    loop :: Context            -- ^ Prune state, to handle the congurece closure
         -> [Prop]             -- ^ Equations to process
         -> [Prop]             -- ^ Equations processed, but failed
         -> [Prop]             -- ^ Equations proved
         -> Bool               -- ^ Managed to prove something this round
         -> IO ([Prop],[Prop]) -- ^ Resulting theorems and unproved
    loop _  []  failed proved False = return (proved,failed)
    loop ps []  failed proved True  = do putStrLn "Loop!"
                                         loop ps failed [] proved False
    loop ps eqs failed proved retry = do

      let discard :: Prop -> [Prop] -> Bool
          discard eq = \failedacc ->
                            any (isomorphicTo (propQSTerms eq))
                                (map propQSTerms failedacc)
                         || evalEQ ps (unifiable (propQSTerms eq))

          (renamings,try,next) = getUpTo batchsize discard eqs failed

      unless (null renamings) $ putStrLn $
         let n = length renamings
         in if (n > 4)
               then "Discarding " ++ show n ++ " renamings and subsumptions."
               else "Discarding renamings and subsumptions: "
                       ++ csv (map (showEquation sig . propQSTerms) renamings)

      res <- tryProve halt_env params try theory proved

      let (successes,without_induction,failures) = partitionInvRes res
          prunable = successes ++ without_induction

      if null prunable
          then loop ps next (failed ++ failures) proved retry
          else do
              let ps' :: Context
                  ps' = execEQ ps (mapM_ (unify . propQSTerms) prunable)

                  failed' :: [Prop]
                  failed' = failed ++ failures

                  -- Interesting candidates
                  (cand,failed_wo_cand)
                      = first (nubSortedOn propQSTerms . concat)
                      $ flip runState failed'
                      $ forM prunable
                      $ \prop -> do
                           failed <- get
                           let (cand,failed') = instancesOf ps prop failed
                           put failed'
                           return cand

              if interesting_cands
                  then do
                      unless (null cand) . putStrLn $
                        "Interesting candidates: "
                          ++ csv (map (showEquation sig . propQSTerms) cand)
                      loop ps' (cand ++ next) failed_wo_cand
                               (proved ++ successes) True

                  else loop ps' next failed' (proved ++ successes) True


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
    instancesOf ps new = partition (instanceOf ps new)

    instanceOf :: Context -> Prop -> Prop -> Bool
    instanceOf ps (propQSTerms -> new) (propQSTerms -> cand) =
      evalEQ ps (new --> cand)
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
    let sig = signature sig0
    (theory,halt_env,props,str_marsh,params@Params{..}) <- processFile file
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

        qsprops = map (eqToProp str_marsh) eqs

    putStrLn "Starting to prove..."

    (qslemmas,qsunproved) <- deep halt_env params theory sig univ qsprops

    (unproved,proved) <- parLoop halt_env params theory props qslemmas

    printInfo unproved proved

    unless dont_print_unproved $
        putStrLn $ "Unproved from QuickSpec: "
            ++ intercalate ", " (map (showEquation sig . propQSTerms) qsunproved)

    when quickspec $
         (writeFile (file++"_QuickSpecOutput.txt") ("All stuff from QuickSpec:\n" ++ intercalate "\n"
         (map show (classToEqs classes))))
