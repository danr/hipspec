{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
module HipSpec.Complement (complement,lint) where

import Control.Monad

import Bag
import Id
import CoreLint
import CoreSyn

import Data.List
import Data.Void

import Halo.BackgroundTheory
import Halo.Binds
import Halo.Lift
import Halo.Monad
import Halo.Pointer
import Halo.RemoveDefault
import Halo.Shared
import Halo.Util

import HipSpec.Monad
import HipSpec.Trans.Theory

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
    Info{halo_env} <- getInfo
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
generateVarTheory v = case realIdUnfolding v of

    CoreUnfolding{uf_tmpl} -> do

        Params{..} <- getParams

        let bs = [NonRec v uf_tmpl]

        (b_lifted,_msgs_lift) <- withUniqSupply (caseLetLift bs case_lift_inner)

        when db_core_lint $ lint "LIFTED" b_lifted

        b_with_defs <- withUniqSupply (removeDefaults b_lifted)

        when db_core_lint $ lint "FINAL" b_with_defs

        when dump_defns $ liftIO $ do
            putStrLn "== DEFNS =="
            putStrLn $ showOutputable b_with_defs

        haloHS (map vacuous `fmap` trBinds b_with_defs)

    u -> fail $ "No unfolding: " ++ showOutputable u

lint :: String -> [CoreBind] -> HS ()
lint s bs = liftIO $ do
    putStrLn $ "== " ++ s ++ " CORE LINT =="
    let (msgs1,msgs2) = lintCoreBindings bs
    mapM_ (mapBagM_ (putStrLn . portableShowSDoc)) [msgs1,msgs2]

