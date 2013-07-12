{-# LANGUAGE RecordWildCards #-}
module Main where

import FreeTyCons

import Read
import Utils

import Data.Char

import CoreToRich
import SimplifyRich
import RichToSimple

import PrettyRich
import PrettyUtils
import PrettyPolyFOL

import Simple as S
import qualified FunctionalFO as FO
import qualified PrettyFO as FO

import SimpleToFO as FO
import Deappify

import qualified ToPolyFOL as P

import LintRich
import CoreLint

import Name
import Unique
import CoreSyn

import TyCon
import DataCon

import Control.Monad
import System.Environment

import Text.PrettyPrint

import System.IO

import qualified Data.Map as M

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

        polyname :: P.Poly (Rename Name) -> String
        polyname x0 = case x0 of
            P.Id x     -> name' x
            P.Ptr x    -> name' x ++ "_ptr"
            P.App      -> "app"
            P.TyFn     -> "fn"
--            P.Proj x i -> "proj_" ++ show i ++ "_" ++ name' x

        mk_kit :: (a -> (Doc,Doc)) -> Kit a
        mk_kit lr
            | show_all_types = (snd . lr,snd . lr)
            | show_types     = (fst . lr,snd . lr)
            | otherwise      = (fst . lr,fst . lr)

        show_typed :: Typed String -> (Doc,Doc)
        show_typed xt@(x ::: _) = (text x,parens (ppTyped text xt))

    let pass  = putStrLn . (++ " ===\n") . ("\n=== " ++) . map toUpper
        putErr = hPutStr stderr

    coreLint cb

    arities <- newIORef $ M.fromList
        [ (Old (dataConName dc),dataConRepArity dc)
        | tc <- bindsTyCons cb
        , dc <- tyConDataCons tc
        ]

    forM_ (flattenBinds cb) $ \ (v,e) -> do
        pass "GHC Core"
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do
                let put      = putStrLn . render
                    put_rich = put . ppFun (mk_kit show_typed) . fmap (fmap name)
                    put_simp = put . ppFun (mk_kit show_typed) . injectFn . fmap (fmap name')
                    put_fo   = put . FO.ppFun text . fmap name'
                    put_poly = put . vcat . map (ppClause text . fmap polyname)

                    put_lints n p = putErr . newline . render . vcat
                                  . map (ppErr text . fmap n) . lint . lintFns . p

                    put_rlint  = put_lints name (:[])
                    put_slint  = put_lints name' (map injectFn)

                pass "Rich"
                put_rich fn
                put_rlint fn

                pass "Rich, simplified"
                let fn' = simpFun fn
                put_rich fn'
                put_rlint fn'

                pass "Simple"
                let simp_fns :: [S.Function (Typed (Rename Name))]
                    simp_fns
                        = uncurry (:)
                        . runRTS
                        . rtsFun
                        . fmap (fmap Old)
                        $ fn'

                mapM_ put_simp simp_fns
                put_slint simp_fns

                pass "First-order functional"
                let fo_fns :: [FO.Function (Rename Name)]
                    fo_fns = map stfFun simp_fns

                mapM_ put_fo fo_fns

                modifyIORef arities $ M.union $ M.fromList
                    [ (fn_name,length fn_args) | FO.Function{..} <- fo_fns ]


                pass "First-order functional, deappified"
                lkup <- fmap (flip M.lookup) (readIORef arities)
                let fo_fns_zapped = mapM zapFn fo_fns lkup
                mapM_ put_fo fo_fns_zapped


                pass "Polymorphic FOL"
                let cls = concatMap P.trFun fo_fns_zapped

                put_poly cls

                return ()
            Left err -> putErr (showOutputable v ++ ": " ++ show err ++ "\n")
        putStrLn ""

newline :: String -> String
newline "" = ""
newline s  = s ++ "\n"
