{-# LANGUAGE RecordWildCards,PatternGuards #-}
module Hip.HipSpec (hipSpec, module Test.QuickSpec.Term) where

import Test.QuickSpec.Term hiding (depth)
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Equations
import Test.QuickSpec.CongruenceClosure

import Hip.Trans.Theory

import Hip.Trans.QSTerm
import Hip.Init
import Hip.MakeInvocations

import Hip.Params

import Halt.Monad
import Halt.Util

import Data.List
import Data.Ord
import Data.Tuple
import Data.Function

import Control.Monad

import System.Console.CmdArgs hiding (summary)

import System.IO


-- (sat p,unsat p (at most n),rest)
getUpTo :: Int -> (a -> [a] -> Bool) -> [a] -> [a] -> ([a],[a],[a])
getUpTo 0 _ xs     _  = ([],[],xs)
getUpTo _ _ []     _  = ([],[],[])
getUpTo n p (x:xs) ys | p x ys    = let (s,u,r) = getUpTo n     p xs (x:ys) in (x:s,  u,r)
                      | otherwise = let (s,u,r) = getUpTo (n-1) p xs (x:ys) in (  s,x:u,r)

deep :: HaltEnv -> Params -> Theory -> [Symbol] -> Int -> [Term Symbol] -> [Prop]
     -> IO ([Prop],[Prop])
deep halt_env params theory ctxt depth univ init_eqs =
    loop (initPrune ctxt univ) init_eqs [] [] False
  where
    chunks = batchsize params

    loop :: PruneState -> [Prop] -> [Prop] -> [Prop] -> Bool -> IO ([Prop],[Prop])
    loop _  []  failed proved False = return (proved,failed)
    loop ps []  failed proved True  = do putStrLn "Loop!"
                                         loop ps failed [] proved False
    loop ps eqs failed proved retry = do

      let (_,cc) = ps

          discard :: Prop -> [Prop] -> Bool
          discard eq = \failedacc ->
                            any (isomorphicTo (propQSTerms eq))
                                (map propQSTerms failedacc)
                         || evalCC cc (uncurry canDerive (propQSTerms eq))

          (renamings,try,next) = getUpTo chunks discard eqs failed

      unless (null renamings) $ putStrLn $
         let n = length renamings
         in if (n > 6) then "Discarding " ++ show n
                               ++ " renamings and subsumptions."
                       else "Discarding renamings and subsumptions: "
                               ++ csv (map (showEq . propQSTerms) renamings)

      res <- tryProve halt_env params try theory proved

      let (successes,without_induction,failures) = partitionInvRes res

          -- This ps' was unused??
          -- (_,ps') = doPrune (const True) ctxt depth
          --                   (map propQSTerms successes) [] ps

          prunable = successes ++ without_induction

      if null prunable
          then loop ps next (failed ++ failures) proved retry
          else do
              let (_,ps') = doPrune (const True) ctxt depth
                                    (map propQSTerms prunable) [] ps
                  failed' = failed ++ failures
              loop ps' next failed' (proved ++ successes) True

{- -- Interesting candidates
                  (cand,failedWoCand) = first (sortBy (comparing equationOrder) . nub . concat)
                                      $ flip runState failed'
                                      $ forM prunable
                                      $ \prop -> do failed <- get
                                                    let eq = propQSTerms prop
                                                        (cand,failed') = instancesOf ps eq failed
                                                    put failed'
                                                    return cand
              unless (null cand) $ putStrLn $ "Interesting candidates: " ++ csv (map showEq cand)
              loop ps' (cand ++ next) failedWoCand (proved ++ successes) True
-}

    isomorphicTo :: Equation -> Equation -> Bool
    e1 `isomorphicTo` e2 =
      case matchEqSkeleton e1 e2 of
        Nothing -> False
        Just xs -> function xs && function (map swap xs)

    matchEqSkeleton :: Equation -> Equation -> Maybe [(Symbol, Symbol)]
    matchEqSkeleton (t, u) (t', u') =
      liftM2 (++) (matchSkeleton t t') (matchSkeleton u u')

    matchSkeleton :: Term Symbol -> Term Symbol -> Maybe [(Symbol, Symbol)]
    matchSkeleton (T.Const f) (T.Const g) | f == g = return []
    matchSkeleton (T.Var x) (T.Var y) = return [(x, y)]
    matchSkeleton (T.App t u) (T.App t' u') =
      liftM2 (++) (matchSkeleton t t') (matchSkeleton u u')
    matchSkeleton _ _ = Nothing

    function :: (Ord a, Eq b) => [(a, b)] -> Bool
    function = all singleton . groupBy ((==) `on` fst) . nub . sortBy (comparing fst)
      where singleton xs = length xs == 1

{-
    instancesOf :: PruneState -> Equation -> [Equation] -> ([Equation],[Equation])
    instancesOf ps new = partition (instanceOf ps new)

    instanceOf :: PruneState -> Equation -> Equation -> Bool
    instanceOf ps new cand =
       let (_,(_,cc)) = doPrune (const True) ctxt depth [cand] [] ps
       in  evalCC cc (uncurry canDerive new)
-}


-- Main library ---------------------------------------------------------------

hipSpec :: FilePath -> [Symbol] -> Int -> IO ()
hipSpec file ctxt depth = do
    hSetBuffering stdout NoBuffering

    params@Params{..} <- cmdArgs defParams

    (theory,halt_env,props,anns) <- processFile params file

    let classToEqs :: [[Term Symbol]] -> [(Term Symbol,Term Symbol)]
        classToEqs = sortBy (comparing (equationOrder . (swap_repr ? swap)))
                   . if quadratic
                          then sort . concatMap uniqueCartesian
                          else concatMap ((\(x:xs) -> zip (repeat x) xs) . sort)

    (quickSpecClasses,prunedEqs) <- packLaws depth ctxt True
                                             (const True) (const True)

    let univ    = concat quickSpecClasses

        eqs     = prepend_pruned ? (prunedEqs ++) $ classToEqs quickSpecClasses

        qsprops = map (uncurry (termsToProp anns)) eqs

    putStrLn "Starting to prove..."

    (qslemmas,qsunproved) <- deep halt_env params theory ctxt depth univ qsprops

    (unproved,proved) <- parLoop halt_env params theory props qslemmas

    printInfo unproved proved

    unless dont_print_unproved $
       putStrLn $ "Unproved from QuickSpec: "
               ++ intercalate "," (map (showEq . propQSTerms) qsunproved)



