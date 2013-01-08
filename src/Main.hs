{-# LANGUAGE NamedFieldPuns,ViewPatterns #-}
module Main where

import HipSpec.Init
import HipSpec.MakeInvocations

import HipSpec.Params

import Control.Monad

import System.Console.CmdArgs hiding (summary)
import System.Exit
import System.FilePath

main :: IO ()
main = do

    Params{files} <- fmap sanitizeParams (cmdArgs defParams)

    when (null files) $ do
        putStrLn "No input files. Run with --help to see possible flags."
        exitFailure

    forM_ files $ \(dropExtension -> file) -> do

        when (file /= head files) $ putStrLn ""
        when (length files > 1)   $ putStrLn $ file ++ ":"

        (theory,halt_env,props,_,params) <- processFile file

        (unproved,proved) <- parLoop halt_env params theory props []

        printInfo unproved proved
