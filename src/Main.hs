{-# LANGUAGE RecordWildCards,ViewPatterns #-}
module Main where

import Hip.Init
import Hip.MakeInvocations

import Hip.Params

import Control.Monad

import System.Console.CmdArgs hiding (summary)
import System.Exit
import System.FilePath

main :: IO ()
main = do

    params@Params{..} <- cmdArgs defParams

    when (null files) $ do
        putStrLn "No input files. Run with --help to see possible flags."
        exitFailure

    forM_ files $ \(dropExtension -> file) -> do

        when (file /= head files) $ putStrLn ""
        when (length files > 1)   $ putStrLn $ file ++ ":"

        (theory,halt_env,props,_) <- processFile params file

        (unproved,proved) <- parLoop halt_env params theory props []

        printInfo unproved proved

