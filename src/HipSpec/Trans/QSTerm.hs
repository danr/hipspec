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

import HipSpec.StringMarshal
import HipSpec.Trans.Property

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.List
import qualified Data.Typeable as Typeable
import Data.Typeable (Typeable)

import CoreSyn as C hiding (Expr)
import GHC hiding (Sig)
import Id
import Type as GhcType
import Var

import Control.Monad

lookupSym :: StrMarsh -> Symbol -> Id
lookupSym m s = fromMaybe (error err_str) (maybeLookupSym m s)
  where
    err_str = "Cannot translate QuickSpec's " ++ show s ++
             " to Core representation! Debug the string marshallings" ++
             " with --db-str-marsh (and --db-names)"

lookupTyCon :: StrMarsh -> Typeable.TyCon -> TyCon
lookupTyCon m s = fromMaybe (error err_str) (maybeLookupTyCon m s)
  where
    err_str = "Cannot translate Data.Typeable type constructor " ++ show s ++
             " to Core representation! Debug the string marshallings" ++
             " with --db-str-marsh (and --db-names)"

typeRepToType :: StrMarsh -> Ty.TypeRep -> Type
typeRepToType str_marsh = go
  where
    go :: Ty.TypeRep -> Type
    go t | Just (ta,tb) <- splitArrow t = go ta `GhcType.mkFunTy` go tb
    go t = let (ty_con,ts) = Ty.splitTyConApp t
           in  lookupTyCon str_marsh ty_con `GhcType.mkTyConApp` map go ts

termToExpr :: StrMarsh -> Map Symbol Var -> Term -> CoreExpr
termToExpr str_marsh var_rename_map = go
  where
    go t = case t of
        T.App e1 e2 -> go e1 `C.App` go e2
        T.Var s   -> C.Var (fromMaybe (err s) (M.lookup s var_rename_map))
        T.Const s -> C.Var (lookupSym str_marsh s)

    err (name -> s) = error $ "QuickSpec's " ++ s ++ " never got a variable"

symbType :: StrMarsh -> Symbol -> Type
symbType str_marsh = typeRepToType str_marsh . symbolType

-- TODO: remove code duplication between this and eqToProp
peqToProp :: Typeable a => Sig -> StrMarsh -> TypedEquation a -> Property PEquation
peqToProp sig str_marsh (e1 :==: e2) = (mk_prop [])
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
        , propType       = typeRepToType str_marsh (termType t1)
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

    term_to_expr = termToExpr str_marsh var_rename_map

    lit = term_to_expr t1 :== term_to_expr t2

    prop_vars = map ((id &&& varType) . snd) var_rename

    var_rename
        = zip occuring_vars
        $ mkVarNamesOfTypeWithOffset 1000
        $ map (symbType str_marsh) occuring_vars

    var_rename_map = M.fromList var_rename

-- TODO: remove code duplication between this and peqToProp
eqToProp :: (Equation -> String) -> StrMarsh -> Equation -> Property Equation
eqToProp show_eq str_marsh eq@(e1 :=: e2) = Property
    { propLiteral    = lit
    , propAssume     = []
    , propVars       = prop_vars
    , propType       = typeRepToType str_marsh (termType e1)
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

    term_to_expr = termToExpr str_marsh var_rename_map

    lit = term_to_expr e1 :== term_to_expr e2

    prop_vars = map ((id &&& varType) . snd) var_rename

    var_rename
        = zip occuring_vars
        $ mkVarNamesOfTypeWithOffset 1000
        $ map (symbType str_marsh) occuring_vars

    var_rename_map = M.fromList var_rename

termType :: Term -> Ty.TypeRep
termType (T.Var s) = symbolType s
termType (T.Const s) = symbolType s
termType (T.App f _x) =
    let (_, [_ty1, ty2]) = Ty.splitTyConApp (termType f)
    in ty2

