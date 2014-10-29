{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, ViewPatterns, ExplicitForAll #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module HipSpec.GHC.Dicts (inlineDicts) where

import HipSpec.GHC.Utils (showOutputable)
import CoreSyn
import IdInfo
import Id
--import HipSpec.GHC.Unfoldings
import Data.List (elemIndex)

import Data.Generics.Geniplate

import Type
import Literal
import Coercion

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,Expr a) |]

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,[Bind a]) |]

-- | Maybe the unfolding of an Id
maybeUnfolding :: Id -> Maybe CoreExpr
maybeUnfolding v = case realIdUnfolding v of
    CoreUnfolding{uf_tmpl} -> Just uf_tmpl
    _                      -> Nothing

inlineDicts :: TransformBi (Expr Id) t => t -> t
inlineDicts = transformBi $ \ e0 -> case e0 of
    App (App (Var f) (Type t)) (Var d)
        | Just cl <- isClassOpId_maybe f
        , DFunId{} <- idDetails d
        -> case (maybeUnfolding f,maybeUnfolding d) of
            (Just (collectBinders -> (_,Case _ _ _ [(_,ss,Var s)])),
             Just (collectArgs -> (_,ks)))
               | Just i <- elemIndex s ss -> drop (length ks - length ss) ks !! i
            x -> e0 -- error $ showOutputable x
    _ -> e0

