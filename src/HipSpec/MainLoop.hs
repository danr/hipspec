{-# LANGUAGE ViewPatterns,NamedFieldPuns,ScopedTypeVariables,RecordWildCards #-}
module HipSpec.MainLoop (mainLoop) where

import HipSpec.Monad
import HipSpec.Property
import HipSpec.ThmLib
import HipSpec.MakeInvocations
import HipSpec.Utils

import Data.List
import Data.Ord
import Data.Maybe

import Control.Monad
import Control.Concurrent.STM

-- | The main loop
mainLoop ::
        TChan (Maybe Property)
     -> [Theorem]                 -- ^ Initial lemmas
     -> HS ([Theorem],[Property]) -- ^ Resulting theorems and conjectures
mainLoop ch thms0 = go False [] thms0
  where
    go True  unproved thms = return (thms,unproved)
                             -- OR: try to prove stuff in unproved
    go False unproved@(uprop:unproved') thms = do
        m_m_prop <- liftIO (atomically (tryReadTChan ch))
        case m_m_prop of
            Nothing -> do
                m_thm <- tryProve uprop thms
                case m_thm of
                    Just thm -> go False unproved' (thm:thms)
                    Nothing  -> go False (unproved' ++ [uprop]) thms
            Just (Just prop) -> do
                m_thm <- tryProve prop thms
                case m_thm of
                    Just thm -> go False unproved (thm:thms)
                    Nothing  -> go False (prop:unproved) thms
            Just Nothing -> go True unproved thms
    go False [] thms = do
        m_prop <- liftIO (atomically (readTChan ch))
        case m_prop of
            Just prop -> do
                m_thm <- tryProve prop thms
                case m_thm of
                    Just thm -> go False [] (thm:thms)
                    Nothing  -> go False [prop] thms
            Nothing -> go True [] thms


