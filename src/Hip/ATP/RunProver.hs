{-# LANGUAGE RecordWildCards #-}
module Hip.ATP.RunProver where

import Prelude hiding (catch)

import Hip.ATP.Results
import Hip.ATP.Provers

import Control.Concurrent

import Control.Exception
import Control.Monad

import System.Process
import System.IO
import System.CPUTime

runProver :: FilePath -> Prover -> String -> Int -> IO ProverResult
runProver filename (Prover{..}) inputStr timelimit = do
--    putStrLn $ "Running prover " ++ show proverName
    (Just inh, Just outh, Just errh, pid) <-
       createProcess (proc proverCmd (proverArgs timelimit))
                     { std_in  = CreatePipe
                     , std_out = CreatePipe
                     , std_err = CreatePipe }

--    putStrLn "Reading output..."
    -- fork off a thread to start consuming the output
    output  <- hGetContents outh
    outMVar <- newEmptyMVar
    void $ forkIO $ evaluate (length output) >> putMVar outMVar ()

    -- fork off a thread to start consuming standard error,
    -- if there is any report it
    unless proverSuppressErrs $ void $ forkIO $ do
        err <- hGetContents errh
        n   <- evaluate (length err)
        when (n > 0) $ do
            hPutStrLn stderr $ "*** " ++ filename ++ " using "
                            ++ show proverName ++ " stderr: ***"
            hPutStrLn stderr err

--    putStrLn "Write and flush input"
    -- now write and flush any input
    when (not (null inputStr)) $ do hPutStr inh inputStr; hFlush inh
    hClose inh -- done with stdin

--    putStrLn "Waiting for result..."
    timeStart <- getCPUTime

    exitCodeMVar <- newEmptyMVar

    tid <- forkIO $ do
         -- read output
         takeMVar outMVar
         hClose outh
         void (return output)
         -- wait on the process
         ex <- waitForProcess pid
         putMVar exitCodeMVar (Just ex)

    kid <- forkIO $ do
         threadDelay (timelimit * 1000 * 1000)
         killThread tid
         terminateProcess pid
         void (waitForProcess pid)
         putMVar exitCodeMVar Nothing

    maybeExitCode <- takeMVar exitCodeMVar

    timeStop <- getCPUTime

    let time = (timeStop - timeStart) `div` (1000*1000)

    killThread tid
    killThread kid

    return $ maybe Failure (const $ proverProcessOutput output time) maybeExitCode


