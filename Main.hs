{-# LANGUAGE RecordWildCards #-}
module Main where

import Read
import Utils

import CoreToRich
import SimplifyRich
import RichToSimple

import PrettyRich
import PrettyType

import Simple as S
import qualified FunctionalFO as FO

import SimpleToFO as FO
import Deappify

import LintRich
import CoreLint

import Name
import Unique
import CoreSyn

import Control.Monad
import System.Environment

import Text.PrettyPrint

import System.IO

import qualified Data.Map as M

import Data.Maybe (catMaybes)
import Data.IORef

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
            if suppress_uniques then "" else '_':showOutputable (getUnique nm)

        name' :: Rename Name -> String
        name' (Old nm) = name nm
        name' (New x)  = '_':show x

        foname :: FOName (Rename Name) -> String
        foname x = case x of
            Orig nm -> name' nm
            Ptr nm  -> name' nm ++ "_ptr"
            FO.App  -> "app"
            X       -> "x"
            Y       -> "y"

        show_typed :: Typed String -> Doc
        show_typed (x ::: t)
            | show_types = parens (hang (text x <+> text "::") 2 (ppType 0 text t))
            | otherwise  = text x

    coreLint cb

    arities <- newIORef M.empty

    forM_ (flattenBinds cb) $ \ (v,e) -> do
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do
                let put = putStrLn . render . ppFun show_typed . fmap (fmap name)
                    put_rlint  = hPutStr stderr . newline . render . vcat . map (ppErr text show_typed . fmap name) . lint . lintFns . (:[])
                    put_slint  = hPutStr stderr . newline . render . vcat . map (ppErr text show_typed . fmap name') . lint . lintFns . map injectFn
                    put_folint = hPutStr stderr . newline . render . vcat . map (ppErr text show_typed . fmap foname) . lint . lintFns . map (fmap FO.toTyped . FO.injectFn)
                put fn
                put_rlint fn
                let fn' = simpFun fn
                put fn'
                put_rlint fn'

                let simp_fns :: [S.Function (Typed (Rename Name))]
                    simp_fns
                        = uncurry (:)
                        . runRTS
                        . rtsFun
                        . fmap (fmap Old)
                        $ fn'
                    put' = putStrLn . render . ppFun show_typed . injectFn . fmap (fmap name')
                mapM_ put' simp_fns
                put_slint simp_fns

                let fo_fns :: [FO.Function (FO.FOTyped (FOName (Rename Name)))]
                    fo_fns = map stfFun simp_fns
                    put'' = putStrLn . render . ppFun (show_typed . FO.toTyped) . FO.injectFn . fmap (fmap foname)
                mapM_ put'' fo_fns
                put_folint fo_fns

                modifyIORef arities $ M.union $ M.fromList $ catMaybes
                    [ case FO.forget_type fn_name of
                        Orig nm -> Just (nm,length fn_args)
                        _       -> Nothing
                    | FO.Function{..} <- fo_fns
                    ]

                lkup <- fmap (flip M.lookup) (readIORef arities)
                let fo_fns_zapped = mapM zapFn fo_fns lkup

                mapM_ put'' fo_fns_zapped
                put_folint fo_fns_zapped
                return ()
            Left err -> print err
        putStrLn ""

newline :: String -> String
newline "" = ""
newline s  = s ++ "\n"
