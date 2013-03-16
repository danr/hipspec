{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards, ScopedTypeVariables, NamedFieldPuns #-}
-- | Getting definitional equations from QuickSpec
module HipSpec.Trans.DefinitionalEquations
    ( pruneWithDefEqs
    , getDefEqs
    , definitionalEquations
    , MakeEquation
    ) where

import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Test.QuickSpec.Equation (Equation(..))
import Test.QuickSpec hiding (vars)
import Test.QuickSpec.Reasoning.PartialEquationalReasoning (PEquation(..))
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Term as T
import Test.QuickSpec.Utils.Typed

import Halo.Shared
import Halo.Subtheory
import Halo.Util
import Halo.FOL.Operations
import qualified Halo.FOL.Internals.Internals as H
import qualified Halo.FOL.Abstract as H

import HipSpec.Monad hiding (equations,vars)
import HipSpec.Reasoning
import HipSpec.StringMarshal
import HipSpec.Trans.QSTerm
import HipSpec.Trans.Theory
import HipSpec.Trans.Unify

import Id
import Name
import Type
import Var

import Prelude hiding (read)

import Data.List
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as M

-- import Debug.Trace
trace :: a -> b -> b
trace = flip const

class MakeEquation eq where
    -- | Makes an equation hold everywhere
    makeEquation :: Equation -> eq

instance MakeEquation Equation where
    makeEquation = id

instance MakeEquation PEquation where
    makeEquation eq@(e1 :=: e2) = nub (vars e1 ++ vars e2) :\/: eq

pruneWithDefEqs :: (MakeEquation eq,EQR eq ctx cc) => Sig -> ctx -> HS ctx
pruneWithDefEqs sig ctx = do
    def_eqs <- getDefEqs sig
    return $ execEQR ctx (mapM_ unify def_eqs)

getDefEqs :: (MakeEquation eq,EQR eq ctx cc) => Sig -> HS [eq]
getDefEqs sig = do

    Info{theory,str_marsh} <- getInfo

    let getFunction s = case s of
            Subtheory (Function v) _ cls _ -> Just (v,formulae cls)
            _ -> Nothing

        func_map = M.fromList (mapMaybe getFunction (subthys theory))

        lookup_func x = fromMaybe [] (M.lookup x func_map)

        def_eqs = definitionalEquations str_marsh lookup_func sig

    writeMsg $ DefinitionalEquations (map (showEquation sig) def_eqs)

    return def_eqs

definitionalEquations
    :: (Signature a,MakeEquation eq)
    => StrMarsh -> (Var -> [H.Formula']) -> a -> [eq]
definitionalEquations str_marsh lookup_var sig =
    trace ("Sig syms: " ++ show sig_syms) $
    concatMap (map makeEquation . fetch_sym) sig_syms
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

    fetch_sym :: Symbol -> [Equation]
    fetch_sym s = case maybeLookupSym str_marsh s of
        Just v | not (isDataConId v) ->
            trace ("Trying " ++ showOutputable v ++ " with "
                             ++ show (length (lookup_var v)) ++ " formulas.") $
            concatMap (trFormula type_matcher maybeLookupVar)
                      (lookup_var v)
        _ -> []

sigSyms :: Signature a => a -> [Symbol]
sigSyms = map (some (sym . unConstant)) . TypeRel.toList . constants . signature

sigVars :: Signature a => a -> [Symbol]
sigVars = map (some (sym . unVariable)) . TypeRel.toList . variables . signature

tryMatchTypes :: Signature a => StrMarsh -> a -> [Var] -> [Var -> Maybe Symbol]
tryMatchTypes str_marsh sig =
    trace (concatMap type_repr types_init) $
    \ qs_init ->
       let res = fmap (flip M.lookup) res_map
           res_map = go qs_init types_init
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
          -> (v -> Maybe Symbol) -> H.Formula Var v t -> [Equation]
trFormula mk_lv lf phi = case phi of
    H.Forall vs (H.Equal t1 t2) -> do
        lv <- mk_lv (map fst vs)
        tr lv t1 t2
    H.Equal t1 t2 -> tr (const Nothing) t1 t2
    _ -> []
  where
    tr lv t1 t2 = do
        e1 <- maybeToList (trTerm lf lv t1)
        e2 <- maybeToList (trTerm lf lv t2)
        return (e1 :=: e2)

trTerm :: forall v q t . (v -> Maybe Symbol) -> (q -> Maybe Symbol) -> H.Term q v t -> Maybe T.Term
trTerm lookup_fun lookup_var = go
  where
    lf = fmap T.Const . lookup_fun

    go :: H.Term q v t -> Maybe T.Term
    go t = case t of
        H.Fun f ts    -> apps <$> lf f <*> mapM go ts
        H.Ctor c ts   -> apps <$> lf c <*> mapM go ts
        H.App _ t1 t2 -> T.App <$> go t1 <*> go t2
        H.Ptr f _     -> lf f
        H.QVar v      -> T.Var <$> lookup_var v
        _             -> Nothing

apps :: Term -> [Term] -> Term
apps = foldl T.App

