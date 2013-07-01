module Main where

import Read
import Utils
import Unfoldings
import CoreToRich
import PrettyRich

import Name
import CoreSyn

import Control.Monad
import System.Environment

import Text.PrettyPrint.HughesPJ

main :: IO ()
main = do
    [file] <- getArgs
    cb <- readBinds file
--    putStrLn (showOutputable cb)
    let cb' = fixUnfoldings cb
    forM_ (flattenBinds cb') $ \ (v,e) -> case trDefn v e of
        Right fn -> putStrLn (render (ppFun text (fmap getOccString fn)))
        Left err -> putStrLn (showOutputable (v,e)) >> print err

