module Main where

import Read
import Utils
import CoreToRich
import PrettyRich
import SimplifyRich

import Name
import Unique
import CoreSyn

import Control.Monad
import System.Environment

import Text.PrettyPrint.HughesPJ

main :: IO ()
main = do
    args <- getArgs
    let (opt,file) = case args of
            [f,"-O"] -> (Optimise,f)
            [f]      -> (Don'tOptimise,f)
            _        -> error "Usage: FILENAME [-O]"
    cb <- readBinds opt file
    forM_ (flattenBinds cb) $ \ (v,e) -> do
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do
                let put = putStrLn . render . ppFun text . fmap name
                put fn
                put (simpFun fn)
            Left err -> print err
        putStrLn ""
  where
    name :: Name -> String
    name nm = getOccString nm ++ "_" ++ showOutputable (getUnique nm)

