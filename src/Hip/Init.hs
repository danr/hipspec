{-# LANGUAGE RecordWildCards, DisambiguateRecordFields #-}
module Hip.Init where

import Hip.BuiltinTypes
import Hip.Params
import Hip.StringMarshal
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

processFile :: FilePath -> IO (Theory,HaloEnv,[Prop],StrMarsh,Params)
processFile file = do

    params@Params{..} <- sanitizeParams <$> cmdArgs defParams

    let ds_conf = DesugarConf
                      { debug_float_out = False
                      , core2core_pass  = True
                      }

    (modguts,dflags) <- desugar ds_conf file

    str_marsh <- makeStringMarshallings db_str_marsh modguts

    let unlifted_program = mg_binds modguts

    us <- mkSplitUniqSupply 'f'

    ((lifted_program,_msgs_lift),_us) <-
        (\binds -> caseLetLift binds case_lift_inner us)
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
            , or_discr          = False
            , var_scrut_constr  = var_scrut_constr
            }

        halo_env = mkEnv halo_conf ty_cons_with_builtins core_defns

        binds_thy = case runHaloMsafe halo_env (trBinds core_defns) of
            (Left err,_msg)    -> error $ "Hip.Init, halo says: " ++ err
            (Right (m,_),_msg) -> m

        subtheories = map (setExtraDependencies min) $ binds_thy ++
            mkResultTypeAxioms core_defns ++
            concatMap ($ ty_cons_with_builtins)
                [backgroundTheory halo_conf,mkDomainAxioms,mkMinRecAxioms]


        theory = Theory subtheories

        props = (consistency ? (inconsistentProp:))
              $ mapMaybe trProperty core_props

    return (theory,halo_env,props,str_marsh,params)
