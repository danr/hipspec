{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns #-}
module HipSpec.Monad
    ( HS()
    , runHS
    , writeMsg
    , getParams
    , HSInfo(..)
    , getInfo
    , getMsgs
    , getWriteMsgFun
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
import HipSpec.StringMarshal
import Test.QuickSpec.Signature

import Control.Concurrent.MVar

-- Accessible state
data HSInfo = Info
    { params    :: Params
    , sig       :: Sig
    , theory    :: Theory
    , halo_env  :: HaloEnv
    , str_marsh :: StrMarsh
                -- Symbol -> Maybe TyThing
    }

data HSEnv = HSEnv
    { hs_info     :: HSInfo
    , write_fun   :: Msg -> IO ()
    , get_msg_fun :: IO [(Double,Msg)]
    , write_mutex :: MVar ()
    }

newtype HS a = HS (ReaderT HSEnv IO a)
  deriving (Functor,Applicative,Monad,MonadIO)

runHS :: HS a -> IO a
runHS (HS m) = do
    params_ <- sanitizeParams <$> cmdArgs defParams
    (write_fn, get_msg_fn) <- case json params_ of
        Nothing -> return (\ _ -> return (), return [])
        _ -> mkWriter
    mtx <- newMVar ()
    runReaderT m HSEnv
        { hs_info = Info
            { params      = params_
            , halo_env    = error "halo_env uninitialized"
            , theory      = error "theory uninitalized"
            , str_marsh   = error "str_marsh uninitialized"
            , sig         = error "signature uninitialized"
            }
        , write_fun   = write_fn
        , get_msg_fun = get_msg_fn
        , write_mutex = mtx
        }

getWriteMsgFun :: HS (Msg -> IO ())
getWriteMsgFun = HS $ do
    prms@Params{verbosity} <- asks (params . hs_info)
    w <- asks write_fun
    mtx <- asks write_mutex
    return $ \ m -> when (msgVerbosity m <= verbosity) $ liftIO $ do
        w m
        () <- takeMVar mtx
        putStrLn (showMsg prms m)
        putMVar mtx ()

writeMsg :: Msg -> HS ()
writeMsg m = do
    w <- getWriteMsgFun
    liftIO $ w m

getMsgs :: HS [(Double,Msg)]
getMsgs = HS $ do
    g <- asks get_msg_fun
    liftIO g

getInfo :: HS HSInfo
getInfo = HS $ asks hs_info

getParams :: HS Params
getParams = HS $ asks (params . hs_info)

initialize :: (HSInfo -> HSInfo) -> HS a -> HS a
initialize k (HS m) = HS $
    local
        (\ hse -> hse { hs_info = k (hs_info hse) })
        m

