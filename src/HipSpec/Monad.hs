{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module HipSpec.Monad
    ( HS()
    , runHS
    , writeMsg
    , getMsgs
    , getWriteMsgFun
    , getParams
    , getTheory
    , getHaloEnv
    , liftIO
    , Msg(..)
    , Params(..)
    , initialize
    ) where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader

import System.Console.CmdArgs hiding (summary,verbosity)

import Halo.Monad

import HipSpec.Messages
import HipSpec.Params
import HipSpec.Trans.Theory

import Control.Concurrent.MVar

data HSEnv = HSEnv
    { halo_env    :: HaloEnv
    , theory      :: Theory
    , params      :: Params
    , write_fun   :: Msg -> IO ()
    , get_msg_fun :: IO [(Double,Msg)]
    , write_mutex :: MVar ()
    }

newtype HS a = HS { unHS :: ReaderT HSEnv IO a }
  deriving (Functor,Applicative,Monad,MonadIO)

runHS :: HS a -> IO a
runHS (HS m) = do
    params_ <- sanitizeParams <$> cmdArgs defParams
    (write_fn, get_msg_fn) <- case json params_ of
        Nothing -> return (\ _ -> return (), return [])
        _ -> mkWriter
    mtx <- newMVar ()
    runReaderT m HSEnv
        { halo_env    = error "halo_env uninitialized"
        , theory      = error "theory uninitalized"
        , params      = params_
        , write_fun   = write_fn
        , get_msg_fun = get_msg_fn
        , write_mutex = mtx
        }

getWriteMsgFun :: HS (Msg -> IO ())
getWriteMsgFun = HS $ do
    v <- asks (verbosity . params)
    w <- asks write_fun
    mtx <- asks write_mutex
    return $ \ m -> when (msgVerbosity m <= v) $ liftIO $ do
        w m
        () <- takeMVar mtx
        putStrLn (showMsg m)
        putMVar mtx ()

writeMsg :: Msg -> HS ()
writeMsg m = do
    w <- getWriteMsgFun
    liftIO $ w m

getMsgs :: HS [(Double,Msg)]
getMsgs = HS $ do
    g <- asks get_msg_fun
    liftIO g

getTheory :: HS Theory
getTheory = HS $ asks theory

getParams :: HS Params
getParams = HS $ asks params

getHaloEnv :: HS HaloEnv
getHaloEnv = HS $ asks halo_env

initialize :: HaloEnv -> Theory -> HS a -> HS a
initialize e t = HS . local (\ hse -> hse
    { halo_env = e
    , theory   = t
    }) . unHS

