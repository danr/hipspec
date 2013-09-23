{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns, CPP #-}
module HipSpec.Monad
    ( HS()
    , runHS
    , writeMsg
    , debugWhen
    , whenFlag
    , getParams
    , getEnv
    , Env(..)
    , getMsgs
    , getWriteMsgFun
    , liftIO
    , Msg(..)
    , Params(..)
    , DebugFlag(..)
    , checkLint
    ) where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader

import HipSpec.Messages
import HipSpec.Params
import HipSpec.Theory
import HipSpec.Translate (TyEnv')

import Control.Concurrent.MVar

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Immutable state
data HSEnv = HSEnv
    { params      :: Params
    , env         :: Env
    , write_fun   :: Msg -> IO ()
    , get_msg_fun :: IO [(Double,Msg)]
    , write_mutex :: MVar ()
    }

-- | Public environment
data Env = Env
    { theory    :: Theory
    , arity_map :: ArityMap
    , ty_env    :: TyEnv'
    }

newtype HS a = HS (ReaderT HSEnv IO a)
  deriving (Functor,Applicative,Monad,MonadIO)

-- | Runs the HipSpec monad, but with theory and arity map uninitialized
runHS :: Params -> Env -> HS a -> IO a
runHS p e (HS m) = do
    (write_fn, get_msg_fn) <-
#ifdef SUPPORT_JSON
        case json p of
            Nothing -> return (\ _ -> return (), return [])
            _ -> mkWriter
#else
        mkWriter
#endif
    mtx <- newMVar ()
    runReaderT m HSEnv
        { params      = p
        , env         = e
        , write_fun   = write_fn
        , get_msg_fun = get_msg_fn
        , write_mutex = mtx
        }

getEnv :: HS Env
getEnv = HS $ asks env

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

debugWhen :: DebugFlag -> String -> HS ()
debugWhen flg s = do
    p <- getParams
    whenFlag p flg $ liftIO $ putStrLn s

checkLint :: Maybe String -> HS ()
checkLint (Just s) = error $
    "Internal error, a lint pass failed:\n" ++ s ++
    "\nPlease report this as a bug."
checkLint Nothing  = return ()

