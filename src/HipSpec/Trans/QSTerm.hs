{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards, ScopedTypeVariables #-}
-- | Translating from QuickSpec -> Core
module HipSpec.Trans.QSTerm
    ( typeRepToType
    , eqToProp
    , peqToProp
    ) where


import Test.QuickSpec.Term as T
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Equation
import Test.QuickSpec.Signature(Sig)
import Test.QuickSpec.Reasoning.PartialEquationalReasoning hiding
    (Total,equal,vars)
import qualified Test.QuickSpec.Utils.Typeable as Ty
import Test.QuickSpec.TestTotality

import Halo.Names
import Halo.Util

import HipSpec.GHC.SigMap
import HipSpec.Trans.Property

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.List
import Data.Typeable (Typeable)

import CoreSyn as C hiding (Expr)
import GHC hiding (Sig)
import Id
import Type as GhcType
import Var

import Control.Monad

typeRepToType :: SigMap -> Ty.TypeRep -> Type
typeRepToType sig_map = go
  where
    go :: Ty.TypeRep -> Type
    go t | Just (ta,tb) <- splitArrow t = go ta `GhcType.mkFunTy` go tb
    go t = let (ty_con,ts) = Ty.splitTyConApp t
           in  lookupTyCon sig_map ty_con `GhcType.mkTyConApp` map go ts

termToExpr :: SigMap -> Map Symbol Var -> Term -> CoreExpr
termToExpr sig_map var_rename_map = go
  where
    go t = case t of
        T.App e1 e2 -> go e1 `C.App` go e2
        T.Var s   -> C.Var (fromMaybe (err s) (M.lookup s var_rename_map))
        T.Const s -> C.Var (lookupSym sig_map s)

    err (name -> s) = error $ "QuickSpec's " ++ s ++ " never got a variable"

symbType :: SigMap -> Symbol -> Type
symbType sig_map = typeRepToType sig_map . symbolType

-- TODO: remove code duplication between this and eqToProp
peqToProp :: Typeable a => Sig -> SigMap -> TypedEquation a -> Property PEquation
peqToProp sig sig_map (e1 :==: e2) = (mk_prop [])
    { propOffsprings = fmap concat . forM occuring_vars $ \ partial_one -> do
         isTrue <- testEquation sig e1 e2 partial_one
         if isTrue then
            return [mk_prop [partial_one]]
           else
            return []
    }

  where
    t1 = term e1
    t2 = term e2

    mk_prop :: [Symbol] -> Property PEquation
    mk_prop partials = Property
        { propLiteral    = lit
        , propAssume     =
            [ Total (varType v) (C.Var v)
            | t <- totals
            , let v = var_rename_map M.! t
            ]
        , propVars       = prop_vars
        , propType       = typeRepToType sig_map (termType t1)
        , propName       = repr
        , propRepr       = repr
        , propVarRepr    = map (show . fst) var_rename
        , propOrigin     = Equation (partials :\/: t1 :=: t2)
        , propOffsprings = return []
        , propOops       = False
        }
      where
        repr = showPEquation sig (partials :\/: t1 :=: t2)
        totals = filter (`notElem` partials) $ occuring_vars

    occuring_vars :: [Symbol]
    occuring_vars = nub (vars t1 ++ vars t2)

    term_to_expr = termToExpr sig_map var_rename_map

    lit = term_to_expr t1 :== term_to_expr t2

    prop_vars = map ((id &&& varType) . snd) var_rename

    var_rename
        = zip occuring_vars
        $ mkVarNamesOfTypeWithOffset 1000
        $ map (symbType sig_map) occuring_vars

    var_rename_map = M.fromList var_rename

-- TODO: remove code duplication between this and peqToProp
eqToProp :: (Equation -> String) -> SigMap -> Equation -> Property Equation
eqToProp show_eq sig_map eq@(e1 :=: e2) = Property
    { propLiteral    = lit
    , propAssume     = []
    , propVars       = prop_vars
    , propType       = typeRepToType sig_map (termType e1)
    , propName       = repr
    , propRepr       = repr
    , propVarRepr    = map (show . fst) var_rename
    , propOrigin     = Equation eq
    , propOffsprings = return []
    , propOops       = False
    }
  where
    repr = show_eq eq

    occuring_vars :: [Symbol]
    occuring_vars = nub (vars e1 ++ vars e2)

    term_to_expr = termToExpr sig_map var_rename_map

    lit = term_to_expr e1 :== term_to_expr e2

    prop_vars = map ((id &&& varType) . snd) var_rename

    var_rename
        = zip occuring_vars
        $ mkVarNamesOfTypeWithOffset 1000
        $ map (symbType sig_map) occuring_vars

    var_rename_map = M.fromList var_rename

termType :: Term -> Ty.TypeRep
termType (T.Var s) = symbolType s
termType (T.Const s) = symbolType s
termType (T.App f _x) =
    let (_, [_ty1, ty2]) = Ty.splitTyConApp (termType f)
    in ty2

