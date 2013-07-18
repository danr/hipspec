{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards, ScopedTypeVariables, RecordWildCards #-}
-- | Translating from QuickSpec -> Core
--
--   There are no type variables here, properties could be generalised with a later pass...
module HipSpec.QSTerm (typeRepToType,eqToProp) where

import Test.QuickSpec.Term as T
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Equation as E
import Test.QuickSpec.Signature (disambiguate)

{-
import Test.QuickSpec.Reasoning.PartialEquationalReasoning hiding
    (Total,equal,vars)
-}

import qualified Test.QuickSpec.Utils.Typeable as Ty
-- import Test.QuickSpec.TestTotality

-- import Halo.Names
import Lang.Utils

import HipSpec.GHC.Types
import HipSpec.GHC.SigMap
import HipSpec.Property as P

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.List
-- import Data.Typeable (Typeable)

import Id
import TyCon (tyConName)


import qualified Lang.Simple as S
import qualified Lang.RichToSimple as S
import Lang.CoreToRich (trVar)

import HipSpec.Theory

typeRepToType :: SigMap -> Ty.TypeRep -> S.Type Name'
typeRepToType sig_map = go
  where
    go t | Just (ta,tb) <- splitArrow t = S.ArrTy (go ta) (go tb)
    go t = S.TyCon (S.Old (tyConName (lookupTyCon sig_map ty_con))) (map go ts)
      where  (ty_con,ts) = Ty.splitTyConApp t

symbType :: SigMap -> Symbol -> S.Type Name'
symbType sig_map = typeRepToType sig_map . symbolType

termToExpr :: SigMap -> Map Symbol TypedName' -> Term -> S.Expr TypedName'
termToExpr sig_map var_rename_map = go
  where
    go t = case t of
        T.App e1 e2 -> S.App (go e1) (go e2)
        T.Var s     -> mkVar (fromMaybe (err s) (M.lookup s var_rename_map))
        T.Const s   -> mkVar (trVar' (lookupSym sig_map s))

    mkVar x = S.Var x []

    err (name -> s) = error $ "QuickSpec's " ++ s ++ " never got a variable"

trVar' :: Var -> TypedName'
trVar' x = fmap S.Old $ case trVar x of
    Right x' -> x'
    Left err -> error $ "Error when translating from QuickSpec: " ++ show err
                     ++ " from variable " ++ showOutputable x

eqToProp :: SigInfo -> Equation -> Property Equation
eqToProp SigInfo{..} eq@(e1 E.:=: e2) = Property
    { prop_name      = repr
    , prop_origin    = Equation eq
    , prop_tvs       = []
    , prop_vars      = map snd var_rename
    , prop_goal      = goal
    , prop_assums    = []
    , prop_repr      = repr
    , prop_var_repr  = map (show . fst) var_rename
    }
  where
    repr = show (mapVars disambig e1 E.:=: mapVars disambig e2)

    disambig = disambiguate sig (vars e1 ++ vars e2)

    occuring_vars :: [Symbol]
    occuring_vars = map disambig (nub (vars e1 ++ vars e2))

    term_to_expr = termToExpr sig_map var_rename_map

    goal = term_to_expr e1 P.:=: term_to_expr e2

    var_rename :: [(Symbol,TypedName')]
    var_rename =
        [ (v,S.New [] x S.::: symbType sig_map v)
        | (v,x) <- zip occuring_vars [0..]
        ]

    var_rename_map = M.fromList var_rename

