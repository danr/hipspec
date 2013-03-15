{-# LANGUAGE RecordWildCards, DisambiguateRecordFields #-}
module HipSpec.Init (processFile) where

import Test.QuickSpec.Signature
import Data.Monoid

import HipSpec.Monad

import HipSpec.Execute

import HipSpec.StringMarshal
import HipSpec.Trans.Property
import HipSpec.Trans.SrcRep
import HipSpec.Trans.Theory

import Halo.BackgroundTheory
import Halo.Binds
import Halo.Conf
import Halo.Lift
import Halo.Monad
import Halo.Util
import Halo.Shared
import Halo.Fetch
import Halo.RemoveDefault

import Data.List
import Data.Maybe

import Var
import CoreSyn
import CoreLint
import Bag
import GHC
import HscTypes
import UniqSupply
import TysWiredIn

import Control.Monad

import Data.Void

lint :: String -> [CoreBind] -> HS ()
lint s bs = liftIO $ do
    putStrLn $ "== " ++ s ++ " CORE LINT =="
    let (msgs1,msgs2) = lintCoreBindings bs
    mapM_ (mapBagM_ (putStrLn . portableShowSDoc)) [msgs1,msgs2]

processFile :: ([Property Void] -> HS a) -> HS a
processFile cont = do

    params@Params{..} <- getParams

    exec_res@ExecuteResult{..} <- liftIO (execute file)

    let init_core_binds = mg_binds mod_guts

    -- putStrLn (maybe "" show signature_sig)

    when dump_core $ liftIO $ do
        putStrLn "== INIT CORE =="
        putStrLn $ showOutputable init_core_binds

    when db_core_lint $ lint "INIT" init_core_binds

    let -- Some stuff in this pile of junk contains non-translatable code.
        -- I shouldn't fetch all dependencies :( Only necessary. Meep.
        junk v = any (`isInfixOf` showOutputable (varType v)) $
                     ( guard (not permissive_junk) >>
                     [ "Test."
                     , "GHC.Class"
                     , "GHC.Conc"
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

        (unfoldings,_debug_unfoldings) = fetch (not . junk) init_core_binds

        unlifted_program = unfoldings ++ init_core_binds

    when db_core_lint $ lint "UNFOLDED" unlifted_program

    let ty_cons :: [TyCon]
        ty_cons = insert boolTyCon $ fetchTyCons unlifted_program

    -- putStrLn debug_unfoldings

    us0 <- liftIO $ mkSplitUniqSupply 'f'

    {-
    simply_lifted <- liftIO (lambdaLift dyn_flags unlifted_program)

    when db_core_lint $ lint "SIMPLY LIFTED" simply_lifted
        -}

    let ((lifted_program_with_defaults,_msgs_lift),us1) =
            caseLetLift unlifted_program case_lift_inner us0

    when db_core_lint $ lint "LIFTED" lifted_program_with_defaults

    let (lifted_program,_us2)
            | bottoms   = initUs us1 (removeDefaults lifted_program_with_defaults)
            | otherwise = (lifted_program_with_defaults,us1)

    when db_core_lint $ lint "FINAL" lifted_program
    {-
    flip mapM_ lifted_program $ \cb -> case cb of
        NonRec x _ -> putStrLn $ showOutputable $ (x, varType x)
        _ -> return ()
    -}

    str_marsh <- liftIO $ makeStringMarshallings params exec_res

    let isPropBinder (NonRec x _) | isPropType x = True
        isPropBinder _ = False

        -- Some properties now come in bind groups, so we need this ugly hack
        -- Should not destroy the translation though
        flattenBindGroups = map (uncurry NonRec) . flattenBinds

        (core_props,core_defns) = partition isPropBinder $ flattenBindGroups lifted_program

    liftIO $ do
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
                flip mapM_ (flattenBinds [binder]) $ \ (v,_) -> do
                    putStrLn $ showOutputable v ++ " :: " ++ showOutputable (varType v)
                    putStrLn $ "Prop type: " ++ show (isPropType v) ++
                               ", junk: " ++ show (junk v)

    let halo_conf :: HaloConf
        halo_conf = HaloConf
            { use_bottom         = bottoms
            , var_scrut_constr   = var_scrut_constr
            }

        halo_env = mkEnv halo_conf

        (binds_thy,_msg) = case runHaloMsafe halo_env (trBinds core_defns) of
            (Left err,msg') -> (error $ "HipSpec.Init, halo says: " ++ err,msg')
            (Right m,msg')  -> (m,msg')

        subtheories =
            map (setExtraDependencies params) $ (map vacuous binds_thy) ++
            concatMap ($ ty_cons) (backgroundTheory halo_conf : [mkTotalAxioms | bottoms])

        theory = Theory subtheories

        props = (consistency ? (inconsistentProperty:))
              $ mapMaybe trProperty core_props

    {-
    putStrLn "== MSGS =="

    mapM_ putStrLn msg

    putStrLn "== BINDS =="

    print binds_thy
    -}

    liftIO $ do
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

    initialize
        (\ hs_info -> hs_info
            { theory    = theory
            , halo_env  = halo_env
            , str_marsh = str_marsh
            , sig       = fromMaybe (error "no signature!") signature_sig
                            `mappend` withTests 100
            })
        (cont props)
