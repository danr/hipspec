{-# LANGUAGE RecordWildCards,ViewPatterns #-}
{-

    Find appropriate translations of QuickSpec strings to core
    bindings, data constructors or type constructors.

-}
module HipSpec.StringMarshal
    ( StrMarsh
    , maybeLookupSym
    , makeStringMarshallings
    ) where

import Halo.Shared

import qualified Data.Map as M
import Data.Map (Map)

import Name hiding (varName)
import BasicTypes
import CoreSyn
import DataCon
import GHC
import TyCon
import TysWiredIn
import Var

import Test.QuickSpec.Term

type StrMarsh = (Map String (Var,Bool) -- True: function, False: data constructor
                ,Map String TyCon)

maybeLookupSym :: StrMarsh -> Symbol -> Maybe (Var,Bool)
maybeLookupSym (strToVar,_) (name -> s) = M.lookup s strToVar

makeStringMarshallings :: Bool -> [TyCon] -> [CoreBind] -> IO StrMarsh
makeStringMarshallings debug ty_cons core_binds = do

    let binds = flattenBinds core_binds

        dbmsg s
            | debug     = putStrLn s
            | otherwise = return ()

    varANNs <- sequence $
        [ do dbmsg $ "Function: " ++ name_str ++ " -> " ++ showOutputable v
             return (name_str,(v,True))
        | (v,_) <- binds
        , let name_str = occNameString (getOccName v)
        ] ++
        [ do dbmsg $ "Constructor: " ++ name_str ++ " -> " ++ showOutputable dc
             return (name_str,(v,False))
        | ty_con <- ty_cons
        , isAlgTyCon ty_con
        , DataTyCon dcs _ <- [algTyConRhs ty_con]
        , dc <- dcs
        , let name_str = occNameString (getOccName dc)
              v        = dataConWorkId dc
        ] ++
        [ do dbmsg $ "Bultin constructor: " ++ name_str ++ " -> " ++ showOutputable dc
             return (name_str,(v,False))
        | (_,dc) <- [("True", trueDataCon)
                    ,("False",falseDataCon)
                    ,("[]",   nilDataCon)
                    ,(":",    consDataCon)
                    ,("(,)",  tupleCon BoxedTuple 2)
                    ]
        , let name_str = occNameString (getOccName dc)
              v        = dataConWorkId dc
        ]

    tyANNs <- sequence
        [ do dbmsg $ "Type constructor: " ++ name_str ++ " -> " ++ showOutputable ty_con
             return (name_str,ty_con)
        | ty_con <- ty_cons
        , let name_str = occNameString (getOccName ty_con)
        ]

    let tyANNs' = tyANNs
               ++ [("[]",listTyCon)
                  ,("()",unitTyCon)
                  ,("(,)",tupleTyCon BoxedTuple 2)
                  ]

    return (M.fromList varANNs,M.fromList tyANNs')
