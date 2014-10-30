{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, ViewPatterns, ExplicitForAll #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module HipSpec.GHC.Dicts (inlineDicts,maybeUnfolding) where

import HipSpec.GHC.Utils (showOutputable)
import CoreSyn
import CoreUtils()
import IdInfo
import Id
import Var
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

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,[(a,Expr a)]) |]

-- | Maybe the unfolding of an Id
maybeUnfolding :: Id -> Maybe CoreExpr
maybeUnfolding v = case ri of
    CoreUnfolding{uf_tmpl} -> Just uf_tmpl
    _                      -> Nothing
  where
    ri = realIdUnfolding v

inlineDicts :: TransformBi (Expr Id) t => t -> t
inlineDicts = transformBi $ \ e0 -> case e0 of
    App (App (Var f) (Type t)) (Var d)
        | Just cl <- isClassOpId_maybe f
        , DFunId{} <- idDetails d
        -> case maybeUnfolding f of
            Just (collectBinders -> (_,Case _ _ _ [(_,ss,Var s)]))
              | Just i <- elemIndex s ss -> case realIdUnfolding d of
                DFunUnfolding _ _ es -> drop (length es - length ss) es !! i
                CoreUnfolding{uf_tmpl} ->
                    let (_,es) = collectArgs uf_tmpl
                    in  drop (length es - length ss) es !! i
                x -> e0 -- error $ showOutputable (e0,x)
            x -> e0 -- error $ showOutputable (e0,x)
    _ -> e0


