{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
module HipSpec.Complement (complement) where

import Control.Monad

import Id

import Data.List
import Data.Void

import Halo.BackgroundTheory
import Halo.Binds
import Halo.Monad
import Halo.Pointer
import Halo.Util

import HipSpec.Monad
import HipSpec.Trans.Theory
import HipSpec.PrepareVar

-- | Complements the required content with the missing parts.
--   Enlarges the current theory if necessary.
--
--   The content required should come from the dependencies
--   of the conjecture and the lemmas
complement :: [HipSpecContent] -> HS ()
complement [] = return ()
complement desired_content = do
    thy <- getTheory
    let current_content = map provides thy
        new_content = desired_content \\ current_content
    new_theories <- concatMapM generate new_content
    enlargeTheory new_theories
    complement $ nubSorted $
        concatMap depends new_theories \\ (new_content ++ current_content)

generate :: HipSpecContent -> HS [HipSpecSubtheory]
generate content = do
    p <- getParams
    halo_env <- getHaloEnv
    res <- case content of
        Data ty_con -> single $ fmap (setExtraDependencies p . vacuous)
                              $ tyConSubtheory (conf halo_env) ty_con
        Function v  -> generateVarTheory v
        Pointer v   -> single $ mkPtr v
        AppThy ty   -> return [mkAppThy p ty]
        Specific (TotalThy ty_con) -> single $ mkTotalAxiom ty_con
        Specific Lemma{} -> err "Cannot generate lemmas"
        Specific Conjecture -> err "Cannot generate conjectures"
    writeMsg $ Generated (show content) (show res)
    return res
  where
    err s = fail $ "HipSpec.Complement: generate " ++ show content ++ ":" ++ s

    single :: Monad m => m a -> m [a]
    single m = (:[]) `liftM` m

generateVarTheory :: Var -> HS [HipSpecSubtheory]
generateVarTheory v = do
    bs <- prepareVar v
    haloHS (map vacuous `fmap` trBinds bs)

