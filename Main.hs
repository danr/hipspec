{-# LANGUAGE RecordWildCards #-}
module Main where

import Read
import Utils

import Data.Char

import CoreToRich
import SimplifyRich
import RichToSimple

import PrettyRich
import PrettyUtils

import Simple as S
import qualified FunctionalFO as FO
import qualified PrettyFO as FO

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

    let (opt,(suppress_uniques,(show_types,(show_all_types,file)))) = ($ args) $
            getFlag' "-O" $  -- run core2core optimisation
            getFlag' "-s" $  -- suppress writing uniques
            getFlag' "-t" $  -- show types on binding variables
            getFlag' "-T" $  -- show all types
                \ args' ->
                    case args' of
                        [f] -> f
                        _   -> error "Usage: FILENAME [-O] [-s] [-t] [-T]"

    cb <- readBinds (if opt then Optimise else Don'tOptimise) file

    let name :: Name -> String
        name nm = getOccString nm ++
            if suppress_uniques then "" else '_':showOutputable (getUnique nm)

        name' :: Rename Name -> String
        name' (Old nm) = name nm
        name' (New x)  = '_':show x

        foname :: FO.FOName (Rename Name) -> String
        foname x = case x of
            FO.Orig nm -> name' nm
            FO.Ptr nm  -> name' nm ++ "_ptr"
            FO.App     -> "app"
            FO.X       -> "x"
            FO.Y       -> "y"

        mk_kit :: (a -> (Doc,Doc)) -> Kit a
        mk_kit lr
            | show_all_types = (snd . lr,snd . lr)
            | show_types     = (fst . lr,snd . lr)
            | otherwise      = (fst . lr,fst . lr)

        show_typed :: Typed String -> (Doc,Doc)
        show_typed xt@(x ::: _) = (text x,parens (ppTyped text xt))

        show_fo_typed :: FO.FOTyped String -> (Doc,Doc)
        show_fo_typed xt@(x FO.::: _) = (text x,parens (FO.ppFOTyped text xt))

    let pass  = putStrLn . (++ " ===\n") . ("\n=== " ++) . map toUpper
        putErr = hPutStr stderr

    coreLint cb

    arities <- newIORef M.empty

    forM_ (flattenBinds cb) $ \ (v,e) -> do
        pass "GHC Core"
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do
                let put      = putStrLn . render
                    put_rich = put . ppFun (mk_kit show_typed) . fmap (fmap name)
                    put_simp = put . ppFun (mk_kit show_typed) . injectFn . fmap (fmap name')
                    put_fo   = put . FO.ppFun (mk_kit show_fo_typed) . fmap (fmap foname)

                    put_lints n p = putErr . newline . render . vcat
                                  . map (ppErr text . fmap n) . lint . lintFns . p

                    put_rlint  = put_lints name (:[])
                    put_slint  = put_lints name' (map injectFn)
                    put_folint = put_lints foname (map (fmap FO.toTyped . FO.injectFn))

                pass "Rich"
                put_rich fn
                put_rlint fn

                let fn' = simpFun fn

                pass "Rich, simplified"
                put_rich fn'
                put_rlint fn'

                let simp_fns :: [S.Function (Typed (Rename Name))]
                    simp_fns
                        = uncurry (:)
                        . runRTS
                        . rtsFun
                        . fmap (fmap Old)
                        $ fn'

                pass "Simple"
                mapM_ put_simp simp_fns
                put_slint simp_fns

                let fo_fns :: [FO.Function (FO.Var (Rename Name))]
                    fo_fns = map stfFun simp_fns

                pass "First-order functional"
                mapM_ put_fo fo_fns
                put_folint fo_fns

                modifyIORef arities $ M.union $ M.fromList $ catMaybes
                    [ case FO.forget_type fn_name of
                        FO.Orig nm -> Just (nm,length fn_args)
                        _          -> Nothing
                    | FO.Function{..} <- fo_fns
                    ]

                lkup <- fmap (flip M.lookup) (readIORef arities)
                let fo_fns_zapped = mapM zapFn fo_fns lkup

                pass "First-order functional, deappified"
                mapM_ put_fo fo_fns_zapped
                put_folint fo_fns_zapped
                return ()
            Left err -> putErr (showOutputable v ++ ": " ++ show err ++ "\n")
        putStrLn ""

newline :: String -> String
newline "" = ""
newline s  = s ++ "\n"
