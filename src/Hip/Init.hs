{-# LANGUAGE RecordWildCards #-}
module Hip.Init where

import Hip.Params
import Hip.Trans.Property
import Hip.Trans.SrcRep
import Hip.Trans.Theory

import Halt.Conf
import Halt.Entry
import Halt.Lift
import Halt.Monad
import Halt.Trans
import Halt.Util

import qualified Data.Map as M
import Data.Map (Map)
import Data.List
import Data.Maybe

import Annotations
import BasicTypes
import CoreSyn
import DataCon
import GhcMonad
import GHC
import HscTypes
import Serialized
import TyCon
import TysWiredIn
import UniqSupply
import Var


removeMain :: [CoreBind] -> [CoreBind]
removeMain = filter (not . remove)
  where
    remove (NonRec x _) | isMain x = True
    remove _ = False

builtin :: [TyCon]
builtin = listTyCon : boolTyCon : unitTyCon
        : map (tupleTyCon BoxedTuple) [2..2]
        -- ^ choice: only tuples of size 2 supported!!
        --   TODO:   add a lot of sizes in dependencies
        --           and do proper data dependency

type ANNs = (Map String (Var,Bool) -- True: function, False: data constructor
            ,Map String TyCon)

findingANNs :: ModGuts -> Ghc ANNs
findingANNs mg = do
    let ty_cons = mg_tcs mg ++ builtin

        binds = flattenBinds (mg_binds mg)

        findANN = findGlobalAnns deserializeWithData . NamedTarget

    varANNs <- sequence $ [ (`zip` repeat (v,True)) <$> findANN (varName v)
                          | v <- map fst binds ]
                          ++
                          [ (`zip` repeat (dataConWorkId c,False)) <$> findANN (dataConName c)
                          | ty_con <- ty_cons
                          , let DataTyCon cons _ = algTyConRhs ty_con
                          , c <- cons ]

    tyANNs <- sequence [ (`zip` repeat t) <$> findANN (tyConName t)
                       | t <- ty_cons ]

    let tyANNs' = concat tyANNs
               ++ [("[]",listTyCon)
                  ,("()",unitTyCon)
                  ,("(,)",tupleTyCon BoxedTuple 2)
                  ]
              -- ^ Cannot write {-# ANN type [] "[]" #-} etc for () and (,)
              --   so we add them in an ad-hoc way here.
              --   TODO: Get this information from `bulitin' automatically.

    -- liftIO $ mapM_ print varANNs

    return (M.fromList $ concat varANNs,M.fromList $ tyANNs')

processFile :: Params -> FilePath -> IO (Theory,HaltEnv,[Prop],ANNs)
processFile Params{..} file = do
    let ds_conf = DesugarConf { debug_float_out = False
                              , core2core_pass  = True
                              }

    (anns,(modguts,dflags)) <- desugarWith findingANNs ds_conf file

    let unlifted_program = removeMain . mg_binds $ modguts

    us <- mkSplitUniqSupply 'f'

    ((lifted_program,_msgs_lift),_us) <- (`caseLetLift` us)
                                     <$> lambdaLift dflags unlifted_program

    let isPropBinder (NonRec x _) | isPropType x = True
        isPropBinder _ = False

        (core_props,core_defns) = partition isPropBinder lifted_program

        ty_cons :: [TyCon]
        ty_cons = mg_tcs modguts

        ty_cons_with_builtin :: [TyCon]
        ty_cons_with_builtin = builtin ++ ty_cons

        halt_conf :: HaltConf
        halt_conf = sanitizeConf $ HaltConf
                        { use_min      = False
                        , use_cf       = False
                        , unr_and_bad  = False
                        }

        halt_env = mkEnv halt_conf ty_cons_with_builtin core_defns

        (subtheories,_msgs_trans)
            = translate halt_env ty_cons_with_builtin core_defns

        theory = Theory subtheories

    return (theory,halt_env,inconsistentProp:mapMaybe trProperty core_props,anns)



