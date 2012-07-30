{-# LANGUAGE RecordWildCards #-}
module Hip.Init where

import Hip.Annotations
import Hip.BuiltinTypes
import Hip.Params
import Hip.Trans.Property
import Hip.Trans.SrcRep
import Hip.Trans.Theory

import Halo.BackgroundTheory
import Halo.Binds
import Halo.Conf
import Halo.Entry
import Halo.Lift
import Halo.Monad
import Halo.Util

import Data.List
import Data.Maybe

import CoreSyn
import GHC
import HscTypes
import UniqSupply

import System.Console.CmdArgs hiding (summary)

processFile :: FilePath -> IO (Theory,HaloEnv,[Prop],ANNs,Params)
processFile file = do

    params@Params{..} <- sanitizeParams <$> cmdArgs defParams

    let ds_conf = DesugarConf
                      { debug_float_out = False
                      , core2core_pass  = True
                      }

    (anns,(modguts,dflags)) <- desugarWith (findANNs db_anns) ds_conf file

    let unlifted_program = mg_binds modguts

    us <- mkSplitUniqSupply 'f'

    ((lifted_program,_msgs_lift),_us) <- (`caseLetLift` us)
                                     <$> lambdaLift dflags unlifted_program

    let isPropBinder (NonRec x _) | isPropType x = True
        isPropBinder _ = False

        (core_props,core_defns) = partition isPropBinder lifted_program

        ty_cons :: [TyCon]
        ty_cons = mg_tcs modguts

        ty_cons_with_builtins :: [TyCon]
        ty_cons_with_builtins = builtins ++ ty_cons

        halo_conf :: HaloConf
        halo_conf = sanitizeConf $ HaloConf
            { use_min           = min
            , use_minrec        = min
            , unr_and_bad       = False
            , ext_eq            = True
            , disjoint_booleans = True
            , or_discr          = False
            }

        halo_env = mkEnv halo_conf ty_cons_with_builtins core_defns

        binds_thy = case runHaloMsafe halo_env (trBinds core_defns) of
                            (Left err,_msg)    -> error $ "Hip.Init, halo says: " ++ err
                            (Right (m,_),_msg) -> m

        subtheories_wo_min = binds_thy ++ backgroundTheory halo_conf ty_cons_with_builtins

        subtheories
            | min       = map makeDataDepend subtheories_wo_min
                       ++ mkMinRec ty_cons_with_builtins
            | otherwise = subtheories_wo_min

        theory = Theory subtheories

        props = (consistency ? (inconsistentProp:))
              $ mapMaybe trProperty core_props

    return (theory,halo_env,props,anns,params)
