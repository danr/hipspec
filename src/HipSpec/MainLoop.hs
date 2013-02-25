{-# LANGUAGE RecordWildCards,PatternGuards,ViewPatterns #-}
module HipSpec.MainLoop where

import Test.QuickSpec
import Test.QuickSpec.Term hiding (depth)
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Main
import Test.QuickSpec.Equation
import Test.QuickSpec.Generate
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Reasoning.PartialEquationalReasoning(
  Context, unify, equal, execPEQ, evalPEQ, initial, PEquation(..))

import HipSpec.Trans.Theory
import HipSpec.Trans.Property
import HipSpec.Trans.QSTerm
import HipSpec.Init
import HipSpec.MakeInvocations
import HipSpec.Messages hiding (equations)

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

import Data.Monoid (mappend)

import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B

import System.IO
import Text.Printf

-- | The main loop
deep :: HaloEnv                            -- ^ Environment to run HaloM
     -> Params                             -- ^ Parameters to the program
     -> (Msg -> IO ())                     -- ^ Writer function
     -> Theory                             -- ^ Translated theory
     -> (PEquation -> String)              -- ^ Showing Equations
     -> Context                            -- ^ The initial context
     -> [Property]                         -- ^ Initial equations
     -> IO ([Property],[Property],Context) -- ^ Resulting theorems and unproved
deep halo_env params@Params{..} write theory show_eq ctx0 init_eqs =
    loop ctx0 init_eqs [] [] False
  where
    show_eqs = map (show_eq . propQSTerms)

    loop :: Context                            -- ^ Prune state, to handle the congurece closure
         -> [Property]                         -- ^ Equations to process
         -> [Property]                         -- ^ Equations processed, but failed
         -> [Property]                         -- ^ Equations proved
         -> Bool                               -- ^ Managed to prove something this round
         -> IO ([Property],[Property],Context) -- ^ Resulting theorems and unproved
    loop ctx []  failed proved False = return (proved,failed,ctx)
    loop ctx []  failed proved True  = do putStrLn "Loop!"
                                          loop ctx failed [] proved False
    loop ctx eqs failed proved retry = do

        let discard :: Property -> [Property] -> Bool
            discard eq failedacc
                = any (isoDiscard (propQSTerms eq))
                      (map propQSTerms failedacc)
                || evalPEQ ctx (equal (propQSTerms eq))

            (renamings,try,next_without_offsprings)
                = getUpTo batchsize discard eqs failed

        unless (null renamings) $ do

            let shown = show_eqs renamings
                n     = length renamings

            putStrLn $ if (n > 4)
                then "Discarding " ++ show n ++ " renamings and subsumptions."
                else "Discarding renamings and subsumptions: " ++ csv shown

        res <- tryProve halo_env params write try theory proved

        let (successes,without_induction,failures) = partitionInvRes res

        offsprings <- concatMapM propOffsprings (successes ++ without_induction)

        let next = offsprings ++ next_without_offsprings

            prunable = successes ++ without_induction

            ctx' :: Context
            ctx' = execPEQ ctx (mapM_ (unify . propQSTerms) prunable)

            failed' :: [Property]
            failed' = failed ++ failures

        case () of
            () | null prunable         -> loop ctx next (failed ++ failures) proved retry
               | not interesting_cands -> loop ctx' next failed' (proved ++ successes) True
               | otherwise -> do
                    -- Interesting candidates
                    let (cand,failed_wo_cand)
                            = first (sortBy (comparing propQSTerms))
                            $ partition p failed'
                          where
                            p fail = or [ instanceOf ctx prop fail | prop <- prunable ]

                    unless (null cand) $ do
                        let shown = show_eqs cand
                        write $ Candidates $ shown
                        putStrLn $ "Interesting candidates: " ++ csv shown

                    loop ctx' (cand ++ next) failed_wo_cand
                              (proved ++ successes) True

instanceOf :: Context -> Property -> Property -> Bool
instanceOf ctx (propQSTerms -> new) (propQSTerms -> cand) =
  evalPEQ ctx (new --> cand)
  where
    eq1 --> eq2 = unify eq2 >> equal eq1

-- can we discard the first equation given that the second has failed?
isoDiscard :: PEquation -> PEquation -> Bool
isoDiscard (pre1 :\/: eq1) (pre2 :\/: eq2)
    = eq1 `isomorphicTo` eq2 && pre1 `isSubsetOf` pre2
  where
    a `isSubsetOf` b = null (a \\ b)

-- Renaming
isomorphicTo :: Equation -> Equation -> Bool
e1 `isomorphicTo` e2 =
  case matchEqSkeleton e1 e2 of
    Nothing -> False
    Just xs -> function xs && function (map swap xs)
  where
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
    function
        = all singleton
        . groupBy ((==) `on` fst)
        . nub
        . sortBy (comparing fst)
      where singleton xs = length xs == 1

-- | Get up to n elements satisfying the predicate, those skipped, and the rest
--   (satisfies p,does not satisfy p (at most n),the rest)
getUpTo :: Int -> (a -> [a] -> Bool) -> [a] -> [a] -> ([a],[a],[a])
getUpTo 0 _ xs     _  = ([],[],xs)
getUpTo _ _ []     _  = ([],[],[])
getUpTo n p (x:xs) ys
   | p x ys    = let (s,u,r) = getUpTo n     p xs (x:ys) in (x:s,  u,r)
   | otherwise = let (s,u,r) = getUpTo (n-1) p xs (x:ys) in (  s,x:u,r)
