{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards, ScopedTypeVariables #-}
{-|

   Translating from QuickSpec -> Core

-}
module HipSpec.Trans.QSTerm where


import Test.QuickSpec.Term as T
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Equation
import Test.QuickSpec.Reasoning.PartialEquationalReasoning hiding
    (Total,equal,vars)
import qualified Test.QuickSpec.Utils.Typeable as Ty

import Test.QuickSpec.Signature hiding (vars)
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel

import Halo.Shared
import Halo.Util

import HipSpec.StringMarshal
import HipSpec.Trans.Property
import HipSpec.Trans.Unify

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.List
import Data.Typeable as Typeable

import CoreSyn as C
import GHC
import Id
import Kind
import Name
import SrcLoc
import Type
import Type as GhcType
import Unique
import Var

import Control.Monad

import qualified Halo.FOL.Internals.Internals as H

-- import Debug.Trace
trace :: a -> b -> b
trace = flip const

typeRepToType :: StrMarsh -> Ty.TypeRep -> Type
typeRepToType (_,strToTyCon) = go
  where
    go :: Ty.TypeRep -> Type
    go t | Just (ta,tb) <- splitArrow t   = go ta `GhcType.mkFunTy` go tb
    go t = let (ty_con,ts) = Ty.splitTyConApp t
               _tr r = tyConName ty_con ++ " ~> " ++ portableShowSDoc (pprSourceTyCon r)
           in  fromMaybe a
                (fmap (\r -> {- trace (tr r) -} r `GhcType.mkTyConApp` map go ts)
                      (M.lookup (tyConName ty_con) strToTyCon))
    a :: Type
    a = mkTyVarTy $ mkTyVar
                (mkInternalName (mkUnique 'j' 1337)
                                (mkOccName tvName "a")
                                wiredInSrcSpan) anyKind

termToExpr :: StrMarsh -> Map Symbol Var -> Term -> CoreExpr
termToExpr str_marsh var_rename_map = go
  where
    go t = case t of
        T.App e1 e2 -> go e1 `C.App` go e2
        T.Var s   -> C.Var (fromMaybe (err s) (M.lookup s var_rename_map))
        T.Const s -> C.Var (fst $ lookupSym str_marsh s)

    err (name -> s) = error $ "QuickSpec's " ++ s ++ " never got a variable"

lookupSym :: StrMarsh -> Symbol -> (Var,Bool)
lookupSym (strToVar,_) (name -> s) = fromMaybe err (M.lookup s strToVar)
  where
    err = error err_str
    err_str = "Cannot translate QuickSpec's " ++ s ++
             " to Core representation! Debug the string marshallings" ++
             " with --db-str-marsh "

termsToProp :: (PEquation -> String)              -- ^ Showing Equations
            -> StrMarsh -> Term -> Term -> Property
termsToProp show_eq str_marsh e1 e2 = (mk_prop [])
    { propOffsprings = forM occuring_vars $ \ partial_one -> do
            return (mk_prop [partial_one])
            -- OBS: Add Nick's testing
    }

  where
    mk_prop :: [Symbol] -> Property
    mk_prop partials = Property
        { propLiteral    = lit
        , propAssume     = map (Total . term_to_expr . T.Var)
                         . filter (`notElem` partials)
                         $ occuring_vars
        , propVars       = prop_vars
        , propName       = partial_precond ++ repr
        , propRepr       = partial_precond ++ repr
        , propVarRepr    = map (show . fst) var_rename
        , propOrigin     = PEquation (partials :\/: e1 :=: e2)
        , propOffsprings = return []
        , propFunDeps    = fundeps
        , propOops       = False
        }
      where
        partial_precond = case partials of
          [] -> ""
          xs -> intercalate ", " (map (("partial " ++) . show) xs) ++ " => "

    occuring_vars :: [Symbol]
    occuring_vars = nub (vars e1 ++ vars e2)

    term_to_expr = termToExpr str_marsh var_rename_map

    lit = term_to_expr e1 :== term_to_expr e2

    prop_vars = [ (setVarType v ty,ty)
                | (x,v) <- var_rename
                , let ty = typeRepToType str_marsh (symbolType x)
                ]

    repr = show_eq ([] :\/: e1 :=: e2)

    fundeps  =
        [ v
        | c <- nub (funs e1 ++ funs e2)
        , let (v,is_function_not_constructor) = lookupSym str_marsh c
        , is_function_not_constructor
        ]

    var_rename     =
        [ (x,setVarType v ty)
        | x <- occuring_vars
        , let ty = typeRepToType str_marsh (symbolType x)
        | v <- varNames
        ]

    var_rename_map = M.fromList var_rename

removeOne :: [a] -> [(a,[a])]
removeOne []     = []
removeOne (x:xs) = (x,xs):map (second (x:)) (removeOne xs)

maybeLookupSym :: StrMarsh -> Symbol -> Maybe (Var,Bool)
maybeLookupSym (strToVar,_) (name -> s) = M.lookup s strToVar

definitionalEquations
    :: Signature a => StrMarsh -> (Var -> [H.Formula Var Var]) -> a -> [PEquation]
definitionalEquations str_marsh lookup_var sig =
    trace ("Sig syms: " ++ show sig_syms) $
    concatMap (map add_all_partial . fetch_sym) sig_syms
  where
    sig_syms :: [Symbol]
    sig_syms = nubSortedOn name $ sigSyms sig

    type_matcher :: [Var] -> [Var -> Maybe Symbol]
    type_matcher = tryMatchTypes str_marsh sig

    sig_syms_map :: Map String Symbol
    sig_syms_map = M.fromList [ (name s,s) | s <- sig_syms ]

    maybeLookupVar :: Var -> Maybe Symbol
    maybeLookupVar v =
        trace ("maybeLookupVar " ++ nm ++ " = " ++ show (fmap name res)) $ res

      where
        nm = showOutputable (nameOccName (idName v))
        res = M.lookup nm sig_syms_map

    add_all_partial :: Equation -> PEquation
    add_all_partial eq@(e1 :=: e2) = nub (vars e1 ++ vars e2) :\/: eq

    fetch_sym :: Symbol -> [Equation]
    fetch_sym s = case maybeLookupSym str_marsh s of
        Just (v,True) ->
            trace ("Trying " ++ showOutputable v ++ " with "
                             ++ show (length (lookup_var v)) ++ " formulas.") $
            concatMap (trFormula type_matcher maybeLookupVar)
                      (lookup_var v)
        _ -> []

eqToProp :: (PEquation -> String) -> StrMarsh -> Equation -> Property
eqToProp show_eq str_marsh (t :=: u) = termsToProp show_eq str_marsh t u

csv :: [String] -> String
csv = intercalate ", "

-- | A bunch of _local_ variable names to quantify over
varNames :: [Var]
varNames =
   [ mkLocalId
       (mkInternalName (mkUnique 'w' i) (mkOccName Name.varName n) wiredInSrcSpan)
       (error "QSTerm.varNames: type")
   | i <- [0..]
   | n <- [1..] >>= flip replicateM "xyzwvu"
   ]

sigSyms :: Signature a => a -> [Symbol]
sigSyms = map (some (sym . unConstant)) . TypeRel.toList . constants . signature

sigVars :: Signature a => a -> [Symbol]
sigVars = map (some (sym . unVariable)) . TypeRel.toList . variables . signature

tryMatchTypes :: Signature a => StrMarsh -> a -> [Var] -> [Var -> Maybe Symbol]
tryMatchTypes str_marsh sig =
    trace (concatMap type_repr types_init) $
    \ qs_init ->
       let res = fmap (flip M.lookup) res_map
           res_map = (go qs_init types_init)
       in  trace ("tryMatchTypes: " ++ showOutputable qs_init ++ " = "
                    ++ show (fmap (map snd . M.toList) res_map)) res

  where
    vs = sigVars sig

    types_init :: [(Type,Symbol)]
    types_init = [ (typeRepToType str_marsh (symbolType v),v) | v <- vs ]

    type_repr :: (Type,Symbol) -> String
    type_repr (t,s) = showOutputable t ++ ":" ++ show s ++ ", \n"

    go qs = take 1 . runMatches [ (q,varType q) | q <- qs ]

trFormula :: ([Var] -> [Var -> Maybe Symbol])
          -> (v -> Maybe Symbol) -> H.Formula Var v -> [Equation]
trFormula mk_lv lf phi = case phi of
    H.Forall vs (H.Equal t1 t2) -> do
        lv <- mk_lv vs
        tr lv t1 t2
    H.Equal t1 t2 -> tr (const Nothing) t1 t2
    _ -> []
  where
    tr lv t1 t2 = do
        e1 <- maybeToList (trTerm lf lv t1)
        e2 <- maybeToList (trTerm lf lv t2)
        return (e1 :=: e2)

trTerm :: forall v q . (v -> Maybe Symbol) -> (q -> Maybe Symbol) -> H.Term q v -> Maybe T.Term
trTerm lookup_fun lookup_var = go
  where
    lf = fmap T.Const . lookup_fun

    go :: H.Term q v -> Maybe T.Term
    go t = case t of
        H.Fun f ts  -> apps <$> lf f <*> mapM go ts
        H.Ctor c ts -> apps <$> lf c <*> mapM go ts
        H.App t1 t2 -> T.App <$> go t1 <*> go t2
        H.Ptr f     -> lf f
        H.QVar v    -> T.Var <$> lookup_var v
        _           -> Nothing

apps :: Term -> [Term] -> Term
apps = foldl T.App

