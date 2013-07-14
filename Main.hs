{-# LANGUAGE RecordWildCards #-}
module Main where

import FreeTyCons
import TyCon (isAlgTyCon)

import Read
import Utils

import Data.Char

import Rich as R

import CoreToRich
import SimplifyRich
import RichToSimple

import PrettyRich
import PrettyUtils
import PrettyPolyFOL as Poly
import PrettyAltErgo as AltErgo

import PolyFOL as Poly

import Data.Ord (comparing)
import Data.List (sortBy)

import Escape

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

import Control.Monad
import System.Environment

import Text.PrettyPrint

import System.IO
import System.Exit

import qualified Data.Map as M

import Data.IORef

import System.Process

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
            P.Proj x i -> "proj_" ++ show i ++ "_" ++ name' x
            P.QVar i   -> 'x':show i

        mk_kit :: (a -> (Doc,Doc)) -> Kit a
        mk_kit lr
            | show_all_types = (snd . lr,snd . lr)
            | show_types     = (fst . lr,snd . lr)
            | otherwise      = (fst . lr,fst . lr)

        show_typed :: Typed String -> (Doc,Doc)
        show_typed xt@(x ::: _) = (text x,parens (ppTyped text xt))

        pass   = putStrLn . (++ " ===\n") . ("\n=== " ++) . map toUpper
        putErr = hPutStr stderr

        put      = putStrLn . render
        put_rich = put . ppFun (mk_kit show_typed) . fmap (fmap name)
        put_simp = put . ppFun (mk_kit show_typed) . injectFn . fmap (fmap name')
        put_fo   = put . FO.ppFun text . fmap name'
        put_poly = put . vcat . map (Poly.ppClause text . fmap polyname)
        alt_ergo = render . vcat . map (AltErgo.ppClause (text . escape) . fmap polyname)
        put_alt_ergo = putStrLn . alt_ergo

        put_lints n p = putErr . newline . render . vcat
                      . map (ppErr text . fmap n) . lint . lintFns . p

        put_rlint  = put_lints name (:[])
        put_slint  = put_lints name' (map injectFn)

    coreLint cb

    counter_ref <- newIORef 0

    let tcs          = filter isAlgTyCon (bindsTyCons cb)
        m_data_types = mapM trTyCon tcs

    data_types <- case m_data_types of
        Right dt -> return dt
        Left err -> do
            putErr (show err ++ "\n")
            exitSuccess

    let dcls = P.appAxioms ++ concatMap (P.trDatatype . fmap Old) data_types

    pass "Datatypes, (ttf1 tptp)"
    put_poly dcls

    pass "Datatypes, (Alt-Ergo)"
    put_alt_ergo dcls

    let con_arities = M.fromList
            [ (Old (R.con_name dc),length (R.con_args dc))
            | dt <- data_types
            , dc <- data_cons dt
            ]

    arities <- newIORef con_arities

    clss <- forM (flattenBinds cb) $ \ (v,e) -> do
        putStrLn ""
        pass "GHC Core"
        putStrLn (showOutputable v ++ " = " ++ showOutputable e)
        case trDefn v e of
            Right fn -> do

                pass "Rich"
                put_rich fn
                put_rlint fn

                pass "Rich, simplified"
                let fn' = simpFun fn
                put_rich fn'
                put_rlint fn'

                counter <- readIORef counter_ref

                pass "Simple"
                let simp_fns :: [S.Function (Typed (Rename Name))]
                    (simp_fns,counter') = (fn'' : fns,c')
                      where
                        (fn'',c',fns) = runRTSFrom counter . rtsFun . fmap (fmap Old) $ fn'

                writeIORef counter_ref counter'

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


                pass "Polymorphic FOL (tff1 tptp)"
                let cls = concatMap (uncurry (++) . P.trFun) fo_fns_zapped

                put_poly cls

                pass "Polymorphic FOL (Alt-Ergo)"
                put_alt_ergo cls

                return cls
            Left err -> do
                putErr (showOutputable v ++ ": " ++ show err ++ "\n")
                exitFailure

    pass "Final Alt-Ergo"
    let cls = concat clss

        rank :: Clause a -> Int
        rank Poly.SortSig{} = 0
        rank Poly.TypeSig{} = 1
        rank _              = 2

        mlw = "/tmp/tfp1.mlw"
        thy = alt_ergo (sortBy (comparing rank) (dcls ++ cls))

    putStrLn thy

    writeFile mlw thy
    (exc,out,err) <- readProcessWithExitCode "alt-ergo" [mlw,"-type-only"] ""
    putErr (newline out)
    putErr (newline err)
    exitWith exc

newline :: String -> String
newline "" = ""
newline s  = s ++ "\n"
