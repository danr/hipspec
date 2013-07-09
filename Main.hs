module Main where

import Read
import Utils

import CoreToRich
import SimplifyRich
import RichToSimple

import PrettyRich
import PrettyType

import Simple

import LintRich
import CoreLint

import Name
import Unique
import CoreSyn

import Control.Monad
import System.Environment

import Text.PrettyPrint

import System.IO

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

    let (opt,(suppress_uniques,(show_types,file))) = ($ args) $
            getFlag' "-O" $
            getFlag' "-s" $
            getFlag' "-t" $ \ args' ->
                case args' of
                    [f] -> f
                    _   -> error "Usage: FILENAME [-O] [-s] [-t]"

    cb <- readBinds (if opt then Optimise else Don'tOptimise) file

    let name :: Name -> String
        name nm = getOccString nm ++
            if suppress_uniques then "" else "_" ++ showOutputable (getUnique nm)

        name' :: Rename Name -> String
        name' (Old nm) = name nm
        name' (New x)  = "_" ++ show x

        show_typed :: Typed String -> Doc
        show_typed (x ::: t)
            | show_types = parens (hang (text x <+> text "::") 2 (ppType 0 text t))
            | otherwise  = text x

    coreLint cb

    forM_ (flattenBinds cb) $ \ (v,e) -> do
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do
                let put = putStrLn . render . ppFun show_typed . fmap (fmap name)
                    put_rlint = hPutStr stderr . newline . render . vcat . map (ppErr text show_typed . fmap name) . lint . lintFns . (:[])
                    put_slint = hPutStr stderr . newline . render . vcat . map (ppErr text show_typed . fmap name') . lint . lintFns . map injectFn
                put fn
                put_rlint fn
                let fn' = simpFun fn
                put fn'
                put_rlint fn'
                let simp_fns
                        = uncurry (:)
                        . runRTS
                        . rtsFun
                        . fmap (fmap Old)
                        $ fn'
                    put' = putStrLn . render . ppFun show_typed . injectFn . fmap (fmap name')
                mapM_ put' simp_fns
                put_slint simp_fns
            Left err -> print err
        putStrLn ""

newline :: String -> String
newline "" = ""
newline s  = s ++ "\n"
