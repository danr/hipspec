{-# LANGUAGE ViewPatterns,NamedFieldPuns,ScopedTypeVariables,RecordWildCards #-}
module HipSpec.MainLoop (mainLoop) where

import HipSpec.Reasoning
import HipSpec.Monad
import HipSpec.Property
import HipSpec.ThmLib
import HipSpec.MakeInvocations
import HipSpec.Utils

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
     -> HS ([Theorem eq],[Property eq],ctx) -- ^ Resulting theorems and conjectures
mainLoop ctxt conjs = loop False ctxt conjs []
  where
    show_eqs = map prop_repr

    loop :: Bool                                -- ^ Managed to prove something this round
         -> ctx                                 -- ^ Prune state, to handle the congurece closure
         -> [Property eq]                       -- ^ Equations processed, but failed
         -> [Property eq]                       -- ^ Equations to process
         -> [Theorem eq]                        -- ^ Proved equations
         -> HS ([Theorem eq],[Property eq],ctx) -- ^ Resulting theorems and conjectures
    loop False ctx []  failed thms = return (thms,failed,ctx)
    loop True  ctx []  failed thms = do writeMsg Loop
                                        loop False ctx (reverse failed) [] thms
    loop retry ctx eqs failed thms = do

        Params{..} <- getParams

        let discard :: Property eq -> [Property eq] -> Bool
            discard prop failedacc = case propEquation prop of
                Just eq
                    -> any (isoDiscard eq) (mapMaybe propEquation failedacc)
                    || evalEQR ctx (equal eq)
                _ -> False

            (renamings,m_try,next_eqs) = getOne discard eqs failed

        unless (null renamings) $ writeMsg $ Discarded (show_eqs renamings)

        case m_try of
            Nothing  -> loop retry ctx next_eqs failed thms
            Just try -> do
                r <- tryProve try thms
                case r of
                    Nothing  -> loop retry ctx next_eqs (try:failed) thms
                    Just thm -> do
                        let ctx' = case propEquation (thm_prop thm) of
                                Just eq -> execEQR ctx (unify eq)
                                Nothing -> ctx
                            thms' = thm:thms
                        case () of
                            () | only_user_stated && not (any isUserStated (next_eqs ++ failed))
                                    -> return (thms',next_eqs ++ failed,ctx')
                               | not interesting_cands
                                    -> loop True ctx' next_eqs failed thms'
                               | otherwise -> do
                                    -- Interesting candidates
                                    let (cand,failed_wo_cand)
                                            = first (sortBy (comparing prop_origin))
                                            $ partition p failed
                                          where
                                            p = instanceOf ctx (thm_prop thm)

                                    unless (null cand) $ writeMsg $ Candidates $ show_eqs cand

                                    loop True ctx' (cand ++ next_eqs) failed_wo_cand thms'

    instanceOf :: ctx -> Property eq -> Property eq -> Bool
    instanceOf ctx (propEquation -> Just new) (propEquation -> Just cand) =
        evalEQR ctx (unify cand >> equal new)
    instanceOf _ _ _ = False

getOne
    :: (a -> [a] -> Bool)  -- ^ Can we discard this property?
    -> [a]                 -- ^ Properties to visit
    -> [a]                 -- ^ Failed properties
    -> ([a],Maybe a,[a])   -- ^ Properties to discard, maybe a property to visit, and remaining properties to visit
getOne _ []     _ys = ([],Nothing,[])
getOne p (x:xs) ys
    -- Discard a property
    | p x ys    = let (d,m_p,r) = getOne p xs (x:ys) in (x:d,m_p,r)
    -- Pick this one
    | otherwise = ([],Just x,xs)

