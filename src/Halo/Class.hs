{-

    An attempt to handle class dictionaries

-}
module Halo.Class ( classBinds , dictDeps ) where

import Class
import CoreFVs
import CoreSyn
import GHC (dataConType)
import Id
import Type
import Var
import VarSet
import TyCon

import Halo.Names
import Halo.Subtheory

import Data.Maybe

classBinds :: [TyCon] -> [CoreBind]
classBinds ty_cons =
    [ NonRec method_id $
        flip (foldr Lam) (classTyVars cls ++ [v']) $
            Case (Var v') w' (varType v')
                [(DataAlt dc,xs',Var (xs' !! i))]
    | ty_con <- ty_cons
    , Just cls <- [tyConClass_maybe ty_con]
    , DataTyCon [dc] _ <- [algTyConRhs ty_con]
    , let v:w:xs  = varNames
          [v',w'] = map (`setVarType` (snd . splitFunTys . dropForAlls $ dataConType dc)) [v,w]
          xs'     = zipWith (\u m -> setVarType u (varType m)) xs (classMethods cls)
    , (i,method_id) <- zip [0..] (classMethods cls)
    ]

dictDeps :: CoreExpr -> [Content s]
dictDeps = functions . varSetElems . exprSomeFreeVars (\v -> isId v && isJust (isClassOpId_maybe v))
