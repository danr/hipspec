module Main where

import Read
import Utils

import System.Environment

main :: IO ()
main = do
    [file] <- getArgs
    cb <- readBinds file
    putStrLn (showOutputable cb)

