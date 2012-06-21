{-|

   Finding ANN pragmas from the source file

-}
module Hip.Annotations where

import Hip.BuiltinTypes

import Halo.Shared
import Halo.Util

import qualified Data.Map as M
import Data.Map (Map)

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
import Var

type ANNs = (Map String (Var,Bool) -- True: function, False: data constructor
            ,Map String TyCon)

findANNs :: Bool -> ModGuts -> Ghc ANNs
findANNs debug mg = do
    let ty_cons = mg_tcs mg

        binds = flattenBinds (mg_binds mg)

        findANN = findGlobalAnns deserializeWithData . NamedTarget

        dbmsg s
          | debug     = liftIO $ putStrLn s
          | otherwise = return ()


    varANNs <- sequence $
               [ do dbmsg $ "Searching for definition " ++ idToStr v
                    (`zip` repeat (v,True)) <$> findANN (varName v)
               | v <- map fst binds ]
               ++
               [ do dbmsg $ "Searching for constructor " ++ show c
                    (`zip` repeat (dataConWorkId c,False)) <$> findANN (dataConName c)
               | ty_con <- ty_cons
               , let DataTyCon cons _ = algTyConRhs ty_con
               , c <- cons ]
               ++
               [ do dbmsg $ "Brutally adding builtin constructor " ++ show c
                         ++ " to string " ++ n
                    return [(n,(dataConWorkId c,False))]
               | (n,c) <- [("True",trueDataCon)
                          ,("False",falseDataCon)
                          ,("[]",nilDataCon)
                          ,(":",consDataCon)
                          ,("(,)",tupleCon BoxedTuple 2)
                          ]
               ]

    dbmsg $ "Found defns/cons: " ++ unlines (map show $ concat varANNs)

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


    -- dbmsg $ "Found tycons: " ++ unlines (map show tyANNs')

    return (M.fromList $ concat varANNs,M.fromList $ tyANNs')