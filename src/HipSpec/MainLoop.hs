{-# LANGUAGE ViewPatterns,NamedFieldPuns,ScopedTypeVariables #-}
module HipSpec.MainLoop (mainLoop) where

import HipSpec.Reasoning

import HipSpec.Monad

import HipSpec.Trans.Property
import HipSpec.MakeInvocations

import Halo.Util

import Data.List
import Data.Ord
import Data.Maybe

import Control.Monad

-- | The main loop
mainLoop :: forall eq ctx cc .
        (EQR eq ctx cc)                      -- ^ The equality reasoner
     => ctx                                  -- ^ The initial context
     -> [Property eq]                        -- ^ Initial equations
     -> [Property eq]                        -- ^ Initial failures
     -> [Property eq]                        -- ^ Initial lemmas
     -> HS ([Property eq],[Property eq],ctx) -- ^ Resulting theorems and unproved
mainLoop = loop False
  where
    show_eqs = map propRepr

    loop :: Bool                                 -- ^ Managed to prove something this round
         -> ctx                                  -- ^ Prune state, to handle the congurece closure
         -> [Property eq]                        -- ^ Equations to process
         -> [Property eq]                        -- ^ Equations processed, but failed
         -> [Property eq]                        -- ^ Equations proved
         -> HS ([Property eq],[Property eq],ctx) -- ^ Resulting theorems and unproved
    loop False ctx []  failed proved = return (proved,failed,ctx)
    loop True  ctx []  failed proved = do writeMsg Loop
                                          loop False ctx failed [] proved
    loop retry ctx eqs failed proved = do

        Params{interesting_cands,batchsize} <- getParams

        let discard :: Property eq -> [Property eq] -> Bool
            discard prop failedacc = case propEquation prop of
                Just eq
                    -> any (isoDiscard eq) (mapMaybe propEquation failedacc)
                    || evalEQR ctx (equal eq)
                _ -> False

            (renamings,try,next_without_offsprings)
                = getUpTo batchsize discard eqs failed

        unless (null renamings) $ do

            let shown = show_eqs renamings
                n     = length renamings

            liftIO $ putStrLn $ if (n > 4)
                then "Discarding " ++ show n ++ " renamings and subsumptions."
                else "Discarding renamings and subsumptions: " ++ csv shown

        res <- tryProve try proved

        let (successes,without_induction,failures) = partitionInvRes res

        offsprings <- liftIO $ concatMapM propOffsprings (successes ++ without_induction)

        let next = offsprings ++ next_without_offsprings

            prunable = successes ++ without_induction

            ctx' :: ctx
            ctx' = execEQR ctx (mapM_ unify (mapMaybe propEquation prunable))

            failed' :: [Property eq]
            failed' = failed ++ failures

        case () of
            () | null prunable         -> loop retry ctx next (failed ++ failures) proved
               | not interesting_cands -> loop True ctx' next failed' (proved ++ successes)
               | otherwise -> do
                    -- Interesting candidates
                    let (cand,failed_wo_cand)
                            = first (sortBy (comparing propOrigin))
                            $ partition p failed'
                          where
                            p fail' = or [ instanceOf ctx prop fail' | prop <- prunable ]

                    unless (null cand) $ do
                        let shown = show_eqs cand
                        writeMsg $ Candidates $ shown
                        liftIO $ putStrLn $ "Interesting candidates: " ++ csv shown

                    loop True ctx' (cand ++ next) failed_wo_cand (proved ++ successes)

    instanceOf :: ctx -> Property eq -> Property eq -> Bool
    instanceOf ctx (propEquation -> Just new) (propEquation -> Just cand) =
        evalEQR ctx (unify cand >> equal new)
    instanceOf _ _ _ = False

-- | Get up to n elements satisfying the predicate, those skipped, and the rest
--   (satisfies p,does not satisfy p (at most n),the rest)
getUpTo :: Int -> (a -> [a] -> Bool) -> [a] -> [a] -> ([a],[a],[a])
getUpTo 0 _ xs     _  = ([],[],xs)
getUpTo _ _ []     _  = ([],[],[])
getUpTo n p (x:xs) ys
   | p x ys    = let (s,u,r) = getUpTo n     p xs (x:ys) in (x:s,  u,r)
   | otherwise = let (s,u,r) = getUpTo (n-1) p xs (x:ys) in (  s,x:u,r)

csv :: [String] -> String
csv = intercalate ", "

