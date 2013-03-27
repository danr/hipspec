{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns #-}
module HipSpec.Monad
    ( HS()
    , runHS
    , haloHS
    , writeMsg
    , debugMsg
    , getParams
    , getHaloEnv
    , getTheory
    , enlargeTheory
    , getMsgs
    , getWriteMsgFun
    , liftIO
    , Msg(..)
    , Params(..)
    , initialize
    , withUniqSupply
    ) where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State

import System.Console.CmdArgs hiding (summary,verbosity)

import Halo.Monad

import HipSpec.Messages
import HipSpec.Params
import HipSpec.Trans.Theory

import Control.Concurrent.MVar

import Control.Arrow (first,second)

import UniqSupply

-- Immutable state
data HSEnv = HSEnv
    { params      :: Params
    , halo_env    :: HaloEnv
    , write_fun   :: Msg -> IO ()
    , get_msg_fun :: IO [(Double,Msg)]
    , write_mutex :: MVar ()
    }

-- Mutable state
type HSSt = (Theory,UniqSupply)

newtype HS a = HS (StateT HSSt (ReaderT HSEnv IO) a)
  deriving (Functor,Applicative,Monad,MonadIO)

haloHS :: HaloM a -> HS a
haloHS m = HS $ do
    HSEnv{halo_env} <- ask
    let (a,_) = runHaloM halo_env m
    return a

runHS :: HS a -> IO a
runHS (HS m) = do
    params_ <- sanitizeParams <$> cmdArgs defParams
    (write_fn, get_msg_fn) <- case json params_ of
        Nothing -> return (\ _ -> return (), return [])
        _ -> mkWriter
    mtx <- newMVar ()
    us0 <- liftIO $ mkSplitUniqSupply 'h'
    runReaderT (evalStateT m ([],us0)) HSEnv
        { params      = params_
        , halo_env    = error "halo_env uninitialized"
        , write_fun   = write_fn
        , get_msg_fun = get_msg_fn
        , write_mutex = mtx
        }

getTheory :: HS Theory
getTheory = HS $ gets fst

enlargeTheory :: [HipSpecSubtheory] -> HS ()
enlargeTheory hs = HS $ modify (first (hs ++))

getWriteMsgFun :: HS (Msg -> IO ())
getWriteMsgFun = HS $ do
    prms@Params{verbosity} <- asks params
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

getParams :: HS Params
getParams = HS $ asks params

getHaloEnv :: HS HaloEnv
getHaloEnv = HS $ asks halo_env

initialize :: HaloEnv -> HS a -> HS a
initialize new_env (HS m) = HS $ local (\ hse -> hse { halo_env = new_env }) m

withUniqSupply :: UniqSM a -> HS a
withUniqSupply m = HS $ do
    u <- gets snd
    let (a,u') = initUs u m
    modify (second (const u'))
    return a

debugMsg :: String -> HS ()
debugMsg m = do
    Params{debug} <- getParams
    when debug $ liftIO $ putStrLn m

