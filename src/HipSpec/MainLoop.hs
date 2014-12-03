{-# LANGUAGE ViewPatterns,NamedFieldPuns,ScopedTypeVariables,RecordWildCards #-}
module HipSpec.MainLoop (mainLoop) where

import HipSpec.Monad
import HipSpec.Property
import HipSpec.ThmLib
import HipSpec.MakeInvocations
import HipSpec.Utils

-- import Data.List
-- import Data.Ord
import Data.Maybe

-- import Control.Monad
import Control.Concurrent.STM

readEntireChan :: TChan a -> IO [a]
readEntireChan ch = do
    x <- atomically (tryReadTChan ch)
    case x of
        Just y  -> fmap (y:) (readEntireChan ch)
        Nothing -> return []

-- | The main loop
mainLoop
     :: Params
     -> TChan (Maybe Property)
     -> [Property]                -- ^ Initial properties
     -> [Theorem]                 -- ^ Initial lemmas
     -> HS ([Theorem],[Property]) -- ^ Resulting theorems and conjectures
mainLoop Params{only_user_stated} ch props0 thms0 = go False props0 thms0
  where
    go _     unproved thms | only_user_stated && not (any isUserStated unproved) = return (thms,unproved)
    go True  unproved thms = proveloop unproved [] thms
    go False unproved thms = do
        mprops <- liftIO (readEntireChan ch)
        -- liftIO $ putStrLn ("go: " ++ ppShow mprops)
        (thms',unproved') <- proveloop ([ p | Just p <- mprops ] ++ unproved ) [] thms
        go (any isNothing mprops) unproved' thms'

    proveloop []     stash thms = return (thms,stash)
    proveloop (u:us) stash thms = do
        m_thm <- tryProve u thms
        case m_thm of
            Just thm -> proveloop us stash (thm:thms)
            Nothing  -> proveloop us (stash ++ [u]) thms

