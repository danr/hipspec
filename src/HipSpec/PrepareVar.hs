{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
module HipSpec.PrepareVar (prepareVar) where

import Control.Monad

import Id
import CoreSyn

import Halo.Lift
import Halo.RemoveDefault
import Halo.Shared
import Halo.Unfoldings

import HipSpec.Lint
import HipSpec.Monad

prepareVar :: Var -> HS [CoreBind]
prepareVar v = case unfolding v of

    Just uf_tmpl -> do

        Params{..} <- getParams

        let bs = [NonRec v uf_tmpl]

        (b_lifted,_msgs_lift) <- withUniqSupply (caseLetLift bs case_lift_inner)

        when db_core_lint $ lint "LIFTED" b_lifted

        b_with_defs <- withUniqSupply (removeDefaults b_lifted)

        when db_core_lint $ lint "WITH DEFS" b_with_defs

        let b_with_unfld = fixUnfoldings b_with_defs

        when db_core_lint $ lint "WITH UNFOLDINGS" b_with_unfld

        when dump_core $ liftIO $ do
            putStrLn "== CORE =="
            putStrLn $ showOutputable b_with_unfld

        return b_with_unfld

    _ -> fail $ "HipSpec.PrepareVar.prepareVar: No unfolding for: " ++ showOutputable v

