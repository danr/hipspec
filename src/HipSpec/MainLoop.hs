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
     -> HS ([Theorem eq],[Property eq],ctx) -- ^ Resulting theorems and unthms
mainLoop ctxt conjs lemmas = loop False ctxt conjs [] lemmas
  where
    show_eqs = map propRepr

    loop :: Bool                                -- ^ Managed to prove something this round
         -> ctx                                 -- ^ Prune state, to handle the congurece closure
         -> [Property eq]                       -- ^ Equations processed, but failed
         -> [Property eq]                       -- ^ Equations to process
         -> [Theorem eq]                        -- ^ Equations thms
         -> HS ([Theorem eq],[Property eq],ctx) -- ^ Resulting theorems and unthms
    loop False ctx []  failed thms = return (thms,failed,ctx)
    loop True  ctx []  failed thms = do writeMsg Loop
                                        loop False ctx (reverse failed) [] thms
    loop retry ctx eqs failed thms = do

        Params{interesting_cands,batchsize,only_user_stated} <- getParams

        let discard :: Property eq -> [Property eq] -> Bool
            discard prop failedacc = case propEquation prop of
                Just eq
                    -> any (isoDiscard eq) (mapMaybe propEquation failedacc)
                    || evalEQR ctx (equal eq)
                _ -> False

            (renamings,try,next_eqs_without_offsprings)
                = getUpTo batchsize discard eqs failed

        unless (null renamings) $ writeMsg $ Discarded (show_eqs renamings)

        (new_thms,new_failures) <- tryProve try thms

        offspring_eqs <- liftIO $ concatMapM (propOffsprings . thm_prop) new_thms

        let ctx' = execEQR ctx (mapM_ unify (mapMaybe (propEquation . thm_prop) new_thms))

            eqs' = offspring_eqs ++ next_eqs_without_offsprings

            failed' = new_failures ++ failed

            thms' = thms ++ new_thms

        case () of
            () | only_user_stated && not (any isUserStated (eqs' ++ failed'))
                    -> return (thms',eqs' ++ failed',ctx')
               | not interesting_cands || null new_thms
                    -> loop (retry || not (null new_thms)) ctx' eqs' failed' thms'
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

                    loop True ctx' (cand ++ eqs') failed_wo_cand thms'

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

