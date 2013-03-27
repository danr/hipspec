{-# LANGUAGE RecordWildCards, DisambiguateRecordFields, NamedFieldPuns #-}
module HipSpec.Init (processFile) where

import HipSpec.Monad

import HipSpec.GHC.Entry

import HipSpec.Trans.Property
import HipSpec.Complement
import HipSpec.PrepareVar

import qualified Data.Map as M

import Halo.Subtheory (idToContent)

import Halo.Conf
import Halo.Monad
import Halo.Util
import Halo.Shared

import Data.Maybe

import Control.Monad

import Data.Void

import CoreSyn

processFile :: (Maybe SigInfo -> [Property Void] -> HS a) -> HS a
processFile cont = do

    params@Params{..} <- getParams

    EntryResult{sig_info,prop_ids} <- liftIO (execute params)

    liftIO $ when dump_sig $ putStr (maybe "" (show . sig) sig_info)

    liftIO $ when dump_props $ do
        putStrLn "== PROP IDS =="
        putStrLn $ showOutputable prop_ids

    prop_bs <- concatMapM prepareVar prop_ids

    liftIO $ when dump_props $ do
        putStrLn "== PROP BINDS =="
        putStrLn $ showOutputable prop_bs

    let halo_env = mkEnv HaloConf
            { use_bottom         = bottoms
            , var_scrut_constr   = var_scrut_constr
            }

        core_props = filter ((`elem` prop_ids) . fst) (flattenBinds prop_bs)

        props = (consistency ? (inconsistentProperty:))
              $ mapMaybe (uncurry trProperty) core_props

    initialize halo_env $ do

        let ids = maybe [] (map snd . M.toList . sym_map . sig_map) sig_info

            qs_theory = nubSorted $ map idToContent ids

        -- Generate theory for the QuickSpec functions and constructors, so
        -- it can be used in definitional equations
        complement qs_theory

        cont sig_info props

