module Main where

import Read
import Utils
import CoreToRich
import PrettyRich
import SimplifyRich
import RichToSimple

import Name
import Unique
import CoreSyn

import Control.Monad
import System.Environment

import Text.PrettyPrint.HughesPJ

getFlag :: Eq a => a -> [a] -> (Bool,[a])
getFlag _   []  = (False,[])
getFlag flg (x:xs)
    | flg == x  = (True,xs)
    | otherwise = (b,x:ys)
  where (b,ys) = getFlag flg xs

getFlag' :: Eq a => a -> ([a] -> b) -> [a] -> (Bool,b)
getFlag' flg k xs = (b,k ys)
  where (b,ys) = getFlag flg xs

main :: IO ()
main = do
    args <- getArgs

    let (opt,(suppress_uniques,file)) = ($ args) $
            getFlag' "-O" $
            getFlag' "-s" $ \ args' ->
                case args' of
                    [f] -> f
                    _   -> error "Usage: FILENAME [-O] [-s]"

    cb <- readBinds (if opt then Optimise else Don'tOptimise) file

    let name :: Name -> String
        name nm = getOccString nm ++
            if suppress_uniques then "" else "_" ++ showOutputable (getUnique nm)

    forM_ (flattenBinds cb) $ \ (v,e) -> do
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do
                let put = putStrLn . render . ppFun text . fmap name
                put fn
                let fn' = simpFun fn
                put fn'
                let (simp_fn,simp_fns) = runRTS (rtsFun (fmap Old fn'))
                mapM_ print (map (fmap (fmap name)) (simp_fn:simp_fns))
            Left err -> print err
        putStrLn ""

