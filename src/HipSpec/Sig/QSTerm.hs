{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards, ScopedTypeVariables, RecordWildCards, NamedFieldPuns #-}
-- | Translating from QuickSpec -> Core
--
--   There are no type variables here, properties are to be generalised in a
--   later pass.
module HipSpec.Sig.QSTerm (eqToProp) where

import Test.QuickSpec.Term as T
import Test.QuickSpec.Equation as E
import Test.QuickSpec.Signature (disambiguate, variables)
import Test.QuickSpec.Utils.TypeRel hiding (lookup)
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap

import HipSpec.Read (SigInfo(..))
import HipSpec.Sig.Symbols
import HipSpec.Utils
import HipSpec.Property as P
import qualified HipSpec.Lang.Simple as S

import HipSpec.Params

import HipSpec.Lang.CoreToRich as CTR

import Data.List (intercalate)
import Data.Char

import HipSpec.Id

termToExpr :: SymbolMap -> Term -> S.Expr Id
termToExpr sm = go
  where
    go t = case t of
        T.App e1 e2 -> S.App (go e1) (go e2)
        T.Var s     -> uncurry S.Lcl (lookupVar sm s)
        T.Const s   -> lookupCon sm s

eqToProp :: Params -> SigInfo -> Integer -> Equation -> Property Equation
eqToProp Params{cond_name,isabelle_mode} SigInfo{..} i eq@(e1 E.:=: e2) = Property
    { prop_name      = final_repr
    , prop_id        = QSOrigin "" i
    , prop_origin    = Equation eq
    , prop_tvs       = []
    , prop_vars      = map (lookupVar symbol_map) occuring_vars
    , prop_goal      = goal
    , prop_assums    = [ mk_assum xs | xs <- raw_found_cond_vars ]
    , prop_repr      = final_repr
    , prop_var_repr  = map show occuring_vars
    }
  where
    mk_assum xs = P.equalsTrue
        (foldl S.App (S.Gbl v t ts) (map (uncurry S.Lcl . lookupVar symbol_map) xs))
      where
        Just mono_ty = cond_mono_ty
        Just cd_id   = cond_id
        (v,t,ts) = translateId (either error id (CTR.trType mono_ty)) cd_id

    repr = "(" ++ show_eq e1 ++ ")" ++ eqls ++ "(" ++ show_eq e2 ++ ")"
      where
        show_eq = show . mapVars disambig . mapConsts (on_name g)

        on_name h s = s { name = h (name s) }

        g x = case lookup x isabelleFunctionNames of
            Just y  | isabelle_mode -> y
            _                       -> x

        eqls | isabelle_mode = " = "
             | otherwise     = " == "

    final_repr = show_precond found_cond_vars repr

    raw_found_cond_vars :: [[Symbol]]
    raw_found_cond_vars = map (map find) cond_vars
      where
        find (n, ty) =
          [some (map (sym . unVariable) . unO) vs | vs <- TypeMap.toList (variables sig), either error id (trType ty) == typeRepToType resolve_map (someType vs) ] !! 0 !! n

    found_cond_vars :: [[Symbol]]
    found_cond_vars = map (map disambig) raw_found_cond_vars

    disambig :: Symbol -> Symbol
    disambig = disambiguate sig (vars e1 ++ vars e2 ++ concat raw_found_cond_vars)

    occuring_vars :: [Symbol]
    occuring_vars = map disambig raw_occuring_vars

    raw_occuring_vars :: [Symbol]
    raw_occuring_vars = nubSorted (vars e1 ++ vars e2 ++ concat raw_found_cond_vars)

    term_to_expr = termToExpr symbol_map

    goal = term_to_expr e1 P.:=: term_to_expr e2

    show_precond [] u = u
    show_precond xss u = intercalate conj (map show_one xss) ++ " ==> " ++ u
      where
        conj | isabelle_mode = " & "
             | otherwise     = " && "
        show_one [x, y]
          | all (not . (\c -> isAlphaNum c || c `elem` "'_.")) cond_name =
            show x ++ " " ++ cond_name ++ " " ++ show y
        show_one xs =
          cond_name ++ concat [" " ++ show x | x <- xs ]

isabelleFunctionNames :: [(String, String)]
isabelleFunctionNames =
  [("&&", "\\<and>"),
   (":", "#"),
   ("++", "@"),
   ("reverse", "rev"),
   ("plus_nat", "Groups.plus_class.plus"),
   ("Zero_nat", "Groups.zero_class.zero :: nat"),
   ("one_nat", "Groups.one_class.one"),
   ("less_eq_nat", "<="),
   ("less_nat", "<")]
