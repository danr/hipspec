{-# LANGUAGE RecordWildCards, DisambiguateRecordFields #-}
module HipSpec.Init where

import HipSpec.BuiltinTypes
import HipSpec.Params
import HipSpec.StringMarshal
import HipSpec.Trans.Property
import HipSpec.Trans.SrcRep
import HipSpec.Trans.Theory

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
import TysWiredIn

import Control.Monad
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


    let -- Some stuff in this pile of junk contains non-translatable code.
        -- I shouldn't fetch all dependencies :( Only necessary. Meep.
        junk v = any (`isInfixOf` showOutputable (varType v)) $
                     [ "Test." , "GHC.Class" ] ++
                     ( guard (not permissive_junk) >>
                     [ "GHC.Conc"
                     , "GHC.Exception"
                     , "GHC.Real"
                     , "GHC.Float"
                     , "GHC.Enum"
                     , "GHC.Prim.Int#"
                     , "GHC.Types.Int"
                     , "GHC.Types.Char"
                     , "GHC.Show.ShowS"
                     , "Foreign."
                     , "Data.Typeable"
                     , "Data.Dynamic"
                     , "System."
                     ])

        {-
        -- This makes + to disappear
        init_core_binds' = filter (any (not . junk . fst) . flattenBinds . (:[]))
                                  init_core_binds
                                  -}


        (unfoldings,debug_unfoldings) = fetch (not . junk) init_core_binds

        unlifted_program = unfoldings ++ init_core_binds

        ty_cons :: [TyCon]
        ty_cons = insert boolTyCon $ fetchTyCons unlifted_program

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

    when dump_props $ do
        putStrLn "== PROPS =="
        putStrLn $ showOutputable core_props

    when dump_defns $ do
        putStrLn "== DEFNS =="
        putStrLn $ showOutputable core_defns

    when dump_types $ do
        putStrLn "== TYPES =="
        flip mapM_ (core_defns ++ core_props) $ \ binder -> do
            putStrLn ""
            putStrLn $ "Is prop binder:" ++ show (isPropBinder binder)
            flip mapM_ (flattenBinds [binder]) $ \ (v,e) -> do
                putStrLn $ showOutputable v ++ " :: " ++ showOutputable (varType v)
                putStrLn $ "Prop type: " ++ show (isPropType v) ++
                           ", junk: " ++ show (junk v)

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
            (Left err,msg')    -> (error $ "HipSpec.Init, halo says: " ++ err,msg')
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

    when dump_subthys $ do
        putStrLn "== SUBTHEORIES =="

        mapM_ print subtheories

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



    return (theory,halo_env,props,str_marsh,params)
