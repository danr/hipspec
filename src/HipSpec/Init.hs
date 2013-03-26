{-# LANGUAGE RecordWildCards, DisambiguateRecordFields #-}
module HipSpec.Init (processFile,lint) where

import Test.QuickSpec.Signature
import Data.Monoid

import HipSpec.Monad

import HipSpec.Execute

import HipSpec.StringMarshal
import HipSpec.Trans.Property
import HipSpec.Trans.SrcRep
import HipSpec.Complement

import qualified Data.Map as M

import Halo.Subtheory (idToContent)

import Halo.Conf
import Halo.Monad
import Halo.Util
import Halo.Shared

import Data.Maybe

import CoreSyn

import Control.Monad

import Data.Void

processFile :: (Maybe Sig -> [Property Void] -> HS a) -> HS a
processFile cont = do

    params@Params{..} <- getParams

    exec_res@ExecuteResult{..} <- liftIO (execute file)

    -- putStrLn (maybe "" show signature_sig)

    when dump_core $ liftIO $ do
        putStrLn "== INIT CORE =="
        putStrLn $ showOutputable init_core_binds

    when db_core_lint $ lint "INIT" init_core_binds

    let isPropBinder (x,_) = isPropType x

        core_props = filter isPropBinder $ flattenBinds init_core_binds

    liftIO $ do
        when dump_props $ do
            putStrLn "== PROPS =="
            putStrLn $ showOutputable core_props

    let halo_env = mkEnv HaloConf
            { use_bottom         = bottoms
            , var_scrut_constr   = var_scrut_constr
            }

        props = (consistency ? (inconsistentProperty:))
              $ mapMaybe (uncurry trProperty) core_props

        m_sig = fmap (`mappend` withTests 100) signature_sig

    str_marsh@(ids,_) <- liftIO $ makeStringMarshallings params exec_res

    initialize
        (\ hs_info -> hs_info
            { halo_env  = halo_env
            , str_marsh = str_marsh
            }) $ do

        let qs_theory = nubSorted $ map (idToContent . snd) (M.toList ids)

        -- Generate theory for the QuickSpec functions and constructors, so
        -- it can be used in
        complement qs_theory

        cont m_sig props

