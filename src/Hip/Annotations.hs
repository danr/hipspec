{-|

   Finding ANN pragmas from the source file

-}
module Hip.Annotations where

import Hip.BuiltinTypes

import Halt.Util

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

findANNs :: ModGuts -> Ghc ANNs
findANNs mg = do
    let ty_cons = mg_tcs mg ++ builtins

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