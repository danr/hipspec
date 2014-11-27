{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad

import Data.List (union)

import HipSpec.GHC.Calls
import HipSpec.Monad
import HipSpec.ParseDSL
-- import HipSpec.Property
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

import HipSpec.Heuristics.CallGraph

import HipSpec.Lang.PrettyRich
import HipSpec.Lang.PrettyUtils
import qualified HipSpec.Lang.SimplifyRich as S
-- import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.Rich as R

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

    let (rich_fns_opt,(type_repl_map,dead_constructors)) = S.optimise data_types_d rich_fns

        -- After optimisation, then I# and Int are removed, and replaced
        -- with internal Integer. This cleans up the quick spec resolve maps:
        adjust_sig_info (SigInfo s (ResolveMap cm tm)) = SigInfo s (ResolveMap cm' tm')
          where
            tm' = M.map
                (\ ty -> case M.lookup ty type_repl_map of
                    Just ty2 -> ty2
                    Nothing  -> ty) tm

            cm' = M.map
                (\ (v,pt) -> case M.lookup v dead_constructors of
                    Just ty2 -> error $ "Dead constructor in signature:" ++ ppShow (v,pt,ty2)
                    Nothing -> (v,pt)) cm

        env = error "hbmc undefined env"

    runHS params env $ do

        debugWhen PrintCore $ "\nInit prop_ids\n" ++ showOutputable prop_ids
        debugWhen PrintCore $ "\nInit vars\n" ++ showOutputable vars

        debugWhen PrintCore $ "\nGHC Core\n" ++ showOutputable
            [ (v,GHC.idType v, GHC.idDetails v, e)
            | (v,e) <- binds
            ]

        debugWhen PrintRich $ "\nRich Definitions\n" ++ unlines (map showRich rich_fns)

        debugWhen PrintOptRich $ "\nOptimised Rich Definitions\n" ++ unlines (map showRich rich_fns_opt)

        let is_pure = \ f i -> case f of
                HBMCId (Select _ _)  -> i == 1
                HBMCId (TupleCon ii) -> i == ii
                _                    -> (f,i) `elem` dc_and_arity
              where
                dc_and_arity =
                    [ (H.raw "The",1) ] ++
                    [ (H.raw "UNR",0) ] ++
                    [ (dc,length args)
                    | R.Datatype _tc _ cons _ <- data_types_d
                    , R.Constructor dc args <- cons
                    ]

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

        let hbmc_fns = renameFunctions (filter (isn't_dict_fun . R.fn_name) rich_fns_opt)

        let (ixss,dt_progs) = unzip (map mergeDatatype data_types)

        let data_info = concat ixss

        let gbl_size = 10

        let (fns,insts) = (`evalState` 0) $ do
                get_insts <- mapM mkGet data_types
                arg_insts <- mapM mkArgument data_types
                new_fns <- mapM (mkNew gbl_size) data_types
                fns <- forM hbmc_fns $ \ fn -> do
                    lfn <- liftFunction fn
                    ulfn <- uniquify lfn
                    mf <- monadic ulfn `runMon` is_pure
                    addSwitches data_info mf
                return (new_fns++fns,get_insts++arg_insts)

        liftIO $ do

            putStrLn "{-# LANGUAGE TypeFamilies,GeneralizedNewtypeDeriving,NoMonomorphismRestriction #-}"
            putStrLn "import Symbolic hiding (L(..),Nat(..))"
            putStrLn $ "import " ++ takeBaseName file

            mapM_ (putStrLn . render' . ppProg Don'tShow pkId . uncurry R.Program) dt_progs

            mapM_ (putStrLn . render' . ppInst pkId) insts

            mapM_ (putStrLn . showRich) fns

