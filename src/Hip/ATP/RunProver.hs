{-# LANGUAGE RecordWildCards, PatternGuards #-}
module Hip.ATP.RunProver where

import Prelude hiding (catch)

import Hip.ATP.Results
import Hip.ATP.Provers

import Control.Concurrent

import Control.Exception
import Control.Monad

import System.Process
import System.IO
import System.Exit
import System.CPUTime
import System.Directory

-- ProcessID does not seem to be exported by something sensible
-- runOneProver :: FilePath -> Prover -> String -> Int
--              -> IO (ProcessID,ThreadId,ThreadId,MVar ExitCode,String)
runOneProver filename (Prover{..}) inputStr timelimit = do

    when proverCannotStdin $ do
        exists <- doesFileExist filename
        unless exists $ hPutStrLn stderr $
            "*** " ++ filename ++ " using " ++  show proverName ++
            " must read its input from a file, run with --output ***"

    (Just inh, Just outh, Just errh, pid) <-
         createProcess (proc proverCmd (proverArgs filename timelimit))
                       { std_in  = CreatePipe
                       , std_out = CreatePipe
                       , std_err = CreatePipe }

    output  <- hGetContents outh
    outMVar <- newEmptyMVar
    void $ forkIO $ evaluate (length output) >> putMVar outMVar ()

    unless proverSuppressErrs $ void $ forkIO $ do
        err <- hGetContents errh
        n   <- evaluate (length err)
        when (n > 0) $ hPutStrLn stderr $
            "*** " ++ filename ++ " using " ++ show proverName ++ " stderr: ***"
            ++ "\n" ++ err

    unless (null inputStr || proverCannotStdin) $ do
        hPutStr inh inputStr
        hFlush inh

    hClose inh

    exit_code_mvar <- newEmptyMVar

    tid <- forkIO $ do
         -- read output
         takeMVar outMVar
         hClose outh
         void (return output)
         -- wait on the process
         ex <- waitForProcess pid
         putMVar exit_code_mvar (Just ex)

    kid <- forkIO $ do
         threadDelay (timelimit * 1000 * 1000)
         killThread tid
         terminateProcess pid
         void (waitForProcess pid)
         putMVar exit_code_mvar Nothing

    return (pid,tid,kid,exit_code_mvar,output)

runProver :: FilePath -> Prover -> String -> Int -> IO ProverResult
runProver filename prover inputStr timelimit

    | ParadoxAnd other_prover <- proverName prover = do

        -- Rally paradox and other_prover against each other,
        -- this assumes that they don't GiveUp, i.e.
        -- terminate without Satisfiable/Unsatisfiable as result

        (pid1,tid1,kid1,exit_code_mvar1,output1) <-
            runOneProver filename paradox inputStr timelimit

        (pid2,tid2,kid2,exit_code_mvar2,output2) <-
            runOneProver filename other_prover inputStr timelimit

        -- Now, see who wins

        winner_mvar <- newEmptyMVar

        let terminate_all = do
                mapM_ terminateProcess [pid1,pid2]
                mapM_ (void . waitForProcess) [pid1,pid2]
                mapM_ killThread [tid1,kid1,tid2,kid2]

        rid1 <- forkIO $ do
            mex <- takeMVar exit_code_mvar1
            terminate_all
            -- putStrLn "Paradox wins!"
            putMVar winner_mvar $ outputToResult paradox mex output1

        rid2 <- forkIO $ do
            mex <- takeMVar exit_code_mvar2
            terminate_all
            -- putStrLn $ (show (proverName other_prover)) ++ " wins!"
            putMVar winner_mvar $ outputToResult other_prover mex output2

        result <- takeMVar winner_mvar

        mapM_ killThread [rid1,rid2]

        return result

    | otherwise = do

        (pid,tid,kid,exit_code_mvar,output) <-
            runOneProver filename prover inputStr timelimit

        maybe_exit_code <- takeMVar exit_code_mvar

        killThread tid
        killThread kid

        return $ outputToResult prover maybe_exit_code output

outputToResult :: Prover -> Maybe ExitCode -> String -> ProverResult
outputToResult Prover{..} maybe_exit_code output =

    let result = maybe Failure
                    (const $ proverProcessOutput output
                           $ error "RunProver: I don't have time for time")
                    maybe_exit_code

    in  case proverParseLemmas of
            Just lemma_parser -> case result of
                Success{} -> result { successLemmas = Just (lemma_parser output) }
                _         -> result
            Nothing -> result
