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
import Halo.Shared
import Halo.Fetch
import Halo.Subtheory

import Data.List
import Data.Maybe

import Var
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

    let init_core_binds = mg_binds modguts


    let (unfoldings,debug_unfoldings) = fetch init_core_binds

        -- Some stuff in this pile of junk contains non-translatable code.
        -- I shouldn't fetch all dependencies :( Only necessary. Meep.
        junk bind = any (`isInfixOf` showOutputable bind)
            [ "Test.QuickSpec" {-, " Foreign."
            , "GHC.Ptr", "GHC.Fingerprint", "GHC.Arr", "GHC.IO", "GHC.Conc"
            , "State#", "RealWorld", "Data.Typeable", "CString", "GHC.TopHandler" -}
            ]

        unlifted_program = filter (not . junk) (unfoldings ++ init_core_binds)

        ty_cons :: [TyCon]
        ty_cons = fetchTyCons unlifted_program

    -- putStrLn debug_unfoldings

    us <- mkSplitUniqSupply 'f'

    ((lifted_program,_msgs_lift),_us) <-
        (\binds -> caseLetLift binds case_lift_inner us)
        <$> lambdaLift dflags unlifted_program

    {-
    flip mapM_ lifted_program $ \cb -> case cb of
        NonRec x _ -> putStrLn $ showOutputable $ (x, varType x)
        _ -> return ()
    -}

    str_marsh <- makeStringMarshallings db_str_marsh ty_cons lifted_program

    let isPropBinder (NonRec x _) | isPropType x = True
        isPropBinder _ = False

        -- Some properties now come in bind groups, so we need this ugly hack
        -- Should not destroy the translation though
        flattenBindGroups = map (uncurry NonRec) . flattenBinds

        (core_props,core_defns) = partition isPropBinder $ flattenBindGroups lifted_program

    {-
    putStrLn "== PROPS =="

    putStrLn $ showOutputable core_props

    putStrLn "== DEFNS =="

    putStrLn $ showOutputable core_defns
    -}

    let halo_conf :: HaloConf
        halo_conf = sanitizeConf $ HaloConf
            { use_min           = min
            , use_minrec        = min
            , unr_and_bad       = False
            , ext_eq            = True
            , or_discr          = False
            , var_scrut_constr  = var_scrut_constr
            }

        halo_env = mkEnv halo_conf ty_cons core_defns

        (binds_thy,msg) = case runHaloMsafe halo_env (trBinds core_defns) of
            (Left err,msg')    -> (error $ "Hip.Init, halo says: " ++ err,msg')
            (Right (m,_),msg') -> (m,msg')

    {-
        binds_thy = concatMap (fst . fst . runHaloM halo_env . trOneBind) core_defns
                 ++ fst (runHaloM halo_env trPointers)
    -}

        app_theory = Subtheory
            { provides = AppTheory
            , depends = [ AppOnMin ]
            , description = "This theory uses the app symbol"
            , formulae = []
            }

        subtheories = map (setExtraDependencies min) $ binds_thy ++
            mkResultTypeAxioms core_defns ++
            [ app_theory ] ++
            concatMap ($ ty_cons)
                [backgroundTheory halo_conf,mkDomainAxioms,mkMinRecAxioms]

        theory = Theory subtheories

        props = (consistency ? (inconsistentProp:))
              $ mapMaybe trProperty core_props

    {-
    putStrLn "== MSGS =="

    mapM_ putStrLn msg

    putStrLn "== BINDS =="

    print binds_thy
    -}

    {-
    putStrLn "== SUBTHEORIES =="

    mapM_ print subtheories
    -}

    {-

    flip mapM_ core_defns $ \ def -> do

        case def of
            NonRec x _ -> putStrLn "NonRec"
            _          -> putStrLn "bindgroup"

        putStrLn $ "Definition : " ++ showOutputable def
        let subthys = (fst $ fst $ runHaloM halo_env $ trOneBind def) :: [HipSpecSubtheory]
        flip mapM_ subthys $ \subthy -> do
            putStrLn $ "description: " ++ (description subthy)
            putStr "provides: "
            print (provides subthy)
            putStr "depends: "
            print (depends subthy)
            putStrLn " -- \n "

    -}

    {-

    putStrLn "== DEFNS =="

    mapM_ (putStrLn . showOutputable) core_defns

    putStrLn "== PROPS =="

    mapM_ (putStrLn . showOutputable) core_props

    putStrLn "== TYPES =="

    flip mapM_ (core_defns ++ core_props) $ \ binder -> do
        putStrLn ""
        print $ isPropBinder binder
        flip mapM_ (flattenBinds [binder]) $ \ (v,e) -> do
            putStrLn $ showOutputable v
            putStrLn $ showOutputable (varType v)
            print $ isPropType v
    -}

    return (theory,halo_env,props,str_marsh,params)
