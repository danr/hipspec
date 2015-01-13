{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad

import Data.List (union,partition,intercalate,isInfixOf)

import HipSpec.GHC.Calls
import HipSpec.Monad
import HipSpec.ParseDSL
import HipSpec.Property
import HipSpec.Read
import HipSpec.Translate
import HipSpec.Params
-- import HipSpec.Lint
import HipSpec.Utils
import HipSpec.Id
import HipSpec.Pretty

import HipSpec.Sig.Resolve

import HipSpec.GHC.Utils
import HipSpec.GHC.FreeTyCons
import HipSpec.Lang.RemoveDefault
import HipSpec.GHC.Unfoldings
import HipSpec.GHC.Dicts (inlineDicts)
import HipSpec.Lang.Uniquify

import Data.List.Split (splitOn)
import HipSpec.Heuristics.CallGraph

import HipSpec.Lang.PrettyRich
import HipSpec.Lang.PrettyUtils
import qualified HipSpec.Lang.SimplifyRich as S
-- import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.Rich as R
import qualified HipSpec.Lang.Type as R

import HipSpec.HBMC
import HipSpec.HBMC.Utils as H

import Control.Monad.State

import qualified TyCon
import TyCon (isAlgTyCon)
import TysWiredIn (boolTyCon)
import UniqSupply

import System.Exit
-- import System.Process
import System.FilePath
import System.Directory

import qualified Id as GHC
-- import qualified CoreSubst as GHC
import Var (Var)
-- import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe (isNothing)

import Debug.Trace

main :: IO ()
main = do

    params@Params{..} <- fmap sanitizeParams (cmdArgs defParams)

    whenFlag params PrintParams $ putStrLn (ppShow params)

    maybe (return ()) setCurrentDirectory directory

    EntryResult{..} <- execute params

    let vars = filterVarSet (not . varFromPrelude) $
               unionVarSets (map (transCalls Without) prop_ids)

        callg = idCallGraph (varSetElems vars)

    us0 <- mkSplitUniqSupply 'h'

    let (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ inlineDicts e)
            | v <- varSetElems vars
            , isNothing (GHC.isClassOpId_maybe v)
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter (\ x -> isAlgTyCon x && not (isPropTyCon x))
                     (bindsTyCons' binds `union` extra_tcs `union` [boolTyCon])

        (am_tcs,data_thy,ty_env',data_types_d) = trTyCons tcs

        rich_fns = toRich binds -- ++ [S.fromProverBoolDefn] -- removing convert for now





    -- Remove dictionaries tycons
    let data_types =
            [ dt
            | dt <- data_types_d
            , case tryGetGHCTyCon (R.data_ty_con dt) of
                Just tc -> case TyCon.tyConParent tc of
                    TyCon.ClassTyCon{} -> False -- remove it
                    _                  -> True
                Nothing -> True
            ]

    let isn't_dict_fun x = case tryGetGHCVar x of
            Just i  -> not (GHC.isDictId i)
            Nothing -> True


    let (rich_fns_opt,(type_repl_map,dead_constructors)) = S.optimise data_types_d rich_fns

    let renamed_fns = renameFunctions (filter (isn't_dict_fun . R.fn_name) rich_fns_opt)

        -- Now, split these into properties and non-properties
        is_prop (R.Function _ (R.Forall _ t) _) = isPropType t

        (props_as_rich,hbmc_fns0) = partition is_prop renamed_fns

        hbmc_fns = {- replaceEquality -} hbmc_fns0

        env = error "hbmc undefined env"

        props
            = sortOn prop_name
            $ either (error . show) id
                     (trProperties (toSimp props_as_rich))


    runHS params env $ do

        debugWhen PrintCore $ "\nInit prop_ids\n" ++ showOutputable prop_ids
        debugWhen PrintCore $ "\nInit vars\n" ++ showOutputable vars

        debugWhen PrintCore $ "\nGHC Core\n" ++ showOutputable
            [ (v,GHC.idType v, GHC.idDetails v, e)
            | (v,e) <- binds
            ]

        debugWhen PrintRich $ "\nRich Definitions\n" ++ unlines (map showRich rich_fns)

        debugWhen PrintOptRich $ "\nOptimised Rich Definitions\n" ++ unlines (map showRich rich_fns_opt)

        debugWhen PrintProps $
            "\nProperties in Simple Definitions:\n" ++ unlines (map showRich props_as_rich) ++
            "\nProperties:\n" ++ unlines (map show props)

        let is_pure = \ f i -> case f of
                HBMCId (Select _ _)  -> i == 1
                HBMCId (TupleCon ii) -> i == ii
                _                    -> (f,i) `elem` dc_and_arity
              where
                dc_and_arity =
                    [ (H.api "The",1) ] ++
                    [ (H.api "UNR",0) ] ++
                    [ (dc,length args)
                    | R.Datatype _tc _ cons _ <- data_types_d
                    , R.Constructor dc args <- cons
                    ]

        let (ixss,dt_progs) = unzip (map mergeDatatype data_types)

        let data_info = concat ixss

        let (fns,insts) = (`evalState` 0) $ do
                get_insts <- mapM mkGet data_types
                -- arg_insts <- mapM mkArgument data_types
                -- new_fns <- mapM mkNew data_types
                fns <- forM hbmc_fns $ \ fn -> do
                    lfn <- liftFunction fn
                    trace (showRich lfn) (return ())
                    pfn <- simpleLetOpt <$> untuple lfn
                    trace (showRich pfn) (return ())
                    ulfn <- uniquify pfn
                    mf <- monadic ulfn `runMon` is_pure
                    -- sf <- addSwitches data_info mf
                    trace (showRich mf) (return ())
                    return mf
                prop_fns <- mapM (hbmcProp data_info) props `runMon` is_pure
                let add_check i = any (`isInfixOf` originalId i) (concatMap (splitOn ".") check)
                return ({- new_fns++-}checkFunctions add_check fns++prop_fns,get_insts{-++arg_insts-})

        liftIO $ do

            putStrLn "{-# LANGUAGE TypeFamilies,GeneralizedNewtypeDeriving,NoMonomorphismRestriction #-}"
            putStrLn "import qualified Symbolic"
            putStrLn "import qualified Prelude"
            putStrLn "import Prelude (Bool(..),Maybe(..))"
            putStrLn $ "import " ++ takeBaseName file

            mapM_ (putStrLn . render' . ppProg Don'tShow pkId . uncurry R.Program) dt_progs

            mapM_ (putStrLn . render' . ppInst pkId) insts

            mapM_ (putStrLn . showRich) fns

            putStrLn $ gbl_depth_name ++ " = " ++ show symbolic_depth ++ " :: Prelude.Int"

            putStrLn $ ("main = do {" ++) . (++ "}") $ intercalate "; "
                [ "Prelude.putStrLn " ++ show ("\n====== " ++ name ++ " ======") ++
                  "; Prelude.print Prelude.=<< Symbolic.runH " ++ name
                | prop <- props, let name = ppId (prop_id prop)
                ]


