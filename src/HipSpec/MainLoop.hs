{-# LANGUAGE ViewPatterns,NamedFieldPuns,ScopedTypeVariables #-}
module HipSpec.MainLoop (mainLoop) where

import HipSpec.Reasoning

import HipSpec.Monad

import HipSpec.Trans.Property
import HipSpec.Trans.Obligation
import HipSpec.MakeInvocations

import Halo.Util

import Data.List
import Data.Ord
import Data.Maybe

import Control.Monad

-- | The main loop
mainLoop :: forall eq ctx cc .
        EQR eq ctx cc                       -- The equality reasoner
     => ctx                                 -- ^ The initial context
     -> [Property eq]                       -- ^ Initial conjectures
     -> [Theorem eq]                        -- ^ Initial lemmas
     -> HS ([Theorem eq],[Property eq],ctx) -- ^ Resulting theorems and unproved
mainLoop ctxt conjs lemmas = loop False ctxt conjs [] lemmas
  where
    show_eqs = map propRepr

    loop :: Bool                                -- ^ Managed to prove something this round
         -> ctx                                 -- ^ Prune state, to handle the congurece closure
         -> [Property eq]                       -- ^ Equations processed, but failed
         -> [Property eq]                       -- ^ Equations to process
         -> [Theorem eq]                        -- ^ Equations proved
         -> HS ([Theorem eq],[Property eq],ctx) -- ^ Resulting theorems and unproved
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

        unless (null renamings) $ writeMsg $ Discarded (show_eqs renamings)

        (new_thms,failures) <- tryProve try proved

        let successes = filter (not . definitionalTheorem) new_thms

        offsprings <- liftIO $ concatMapM (propOffsprings . thm_prop) new_thms

        let next = offsprings ++ next_without_offsprings

            ctx' :: ctx
            ctx' = execEQR ctx (mapM_ unify (mapMaybe (propEquation . thm_prop) new_thms))

            failed' :: [Property eq]
            failed' = failed ++ failures

        case () of
            () | null new_thms         -> loop retry ctx next (failed ++ failures) proved
               | not interesting_cands -> loop True ctx' next failed' (proved ++ successes)
               | otherwise -> do
                    -- Interesting candidates
                    let (cand,failed_wo_cand)
                            = first (sortBy (comparing propOrigin))
                            $ partition p failed'
                          where
                            p fail' = or
                                [ instanceOf ctx (thm_prop thm) fail'
                                | thm <- new_thms ]

                    unless (null cand) $ writeMsg $ Candidates $ show_eqs cand

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

