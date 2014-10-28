{-# LANGUAGE RecordWildCards, NamedFieldPuns, DoAndIfThenElse, ViewPatterns, CPP, PatternGuards #-}
module Main where

import QuickSpec.Eval
import QuickSpec.Rules
import QuickSpec.Pretty (prettyPrint)

import HipSpec.Params (SuccessOpt(..))

import HipSpec.ThmLib
import HipSpec.Property hiding (Literal(..))
import HipSpec.Sig.QSTerm
import HipSpec.Init
import HipSpec.Monad hiding (equations)
import HipSpec.MainLoop

import HipSpec.Utils

import Prelude hiding (read)

import qualified Data.Map as M

import Data.List
import Data.List.Split
import Data.Maybe
import Data.Ord
import Data.Function

import Control.Monad

#ifdef SUPPORT_JSON
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B
#endif

import System.Exit (exitSuccess,exitFailure)

import Control.Concurrent.STM
import Control.Monad.IO.Class
import Control.Concurrent

populateChan :: MonadIO m => TChan a -> [a] -> m ()
populateChan ch = liftIO . atomically . mapM_ (writeTChan ch)

main :: IO ()
main = processFile $ \ callg m_sig_info user_props -> do
    writeMsg FileProcessed

    exit_act <- case m_sig_info of

        [] -> do
            ch <- liftIO newTChanIO
            populateChan ch [Nothing]
            runMainLoop ch user_props []

        sig_info@SigInfo{..}:_sig_infos -> do

            p@Params{expand_boolprops} <- getParams
            ch <- runQuickSpec sig_info
            whenFlag p QuickSpecOnly $ liftIO $ forever $ do
                x <- atomically (readTChan ch)
                when (isNothing x) exitSuccess
            runMainLoop ch user_props []

#ifdef SUPPORT_JSON
    Params{json} <- getParams

    case json of
        Just json_file -> do
            msgs <- getMsgs
            liftIO $ B.writeFile json_file (encode msgs)
        Nothing -> return ()
#endif

    exit_act

runMainLoop :: TChan (Maybe Property) -> [Property] -> [Theorem] -> HS (HS ())
runMainLoop ch user_props initial_thms = do

    params@Params{only_user_stated,success,file} <- getParams

    (theorems,conjectures) <- mainLoop params ch user_props initial_thms

    let showProperties ps = [ (prop_name p,maybePropRepr p) | p <- ps ]
        theorems' = map thm_prop
                  . filter (\ t -> not (definitionalTheorem t) || isUserStated (thm_prop t))
                  $ theorems
        notQS  = filter (not . isFromQS)
        fromQS = filter isFromQS

    writeMsg Finished
        { proved      = showProperties $ notQS theorems'
        , unproved    = showProperties $ notQS conjectures
        , qs_proved   = showProperties $ fromQS theorems'
        , qs_unproved =
            if only_user_stated then [] else showProperties $ fromQS conjectures
        }

    let exit_act = liftIO $ case success of
            NothingUnproved -> do
                putStr (file ++ ", " ++ show success ++ ":")
                if null conjectures
                    then putStrLn "ok" >> exitSuccess
                    else putStrLn "fail" >> exitFailure
            ProvesUserStated -> do
                putStr (show success ++ ":")
                if null (notQS conjectures)
                    then putStrLn "ok" >> exitSuccess
                    else putStrLn "fail" >> exitFailure
            CleanRun -> exitSuccess

    return exit_act

runQuickSpec :: SigInfo -> HS (TChan (Maybe Property))
runQuickSpec sig_info@SigInfo{..} = do

    params@Params{..} <- getParams

    ch <- liftIO newTChanIO

    liftIO $ forkIO $ runM sig $ do

        whenFlag params QuickSpecDebug $ rule $ event >>= execute . liftIO . prettyPrint

        rule $ do
            Found p <- event
            let prop = trProp params sig_info 0 p
            let props | expand_boolprops = boolifyProperty prop
                      | otherwise        = [prop]
            execute $ liftIO $ populateChan ch $ map Just props
        quickSpecLoop sig
        -- send finished:
        liftIO (atomically (writeTChan ch Nothing))

    return ch

    {-

    let callg = transitiveCallGraph resolve_map

    debugWhen PrintCallGraph $ "\nCall Graph:\n" ++ unlines
        [ show s ++ " calls " ++ show ss
        | (s,ss) <- M.toList callg
        ]
    -}

