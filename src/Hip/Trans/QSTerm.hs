{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards #-}
{-|

   Translating from QuickSpec -> Core

-}
module Hip.Trans.QSTerm where


import Test.QuickSpec.Term
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Equation
import qualified Test.QuickSpec.Utils.Typeable as Ty

import Halo.Shared

import Hip.StringMarshal
import Hip.Trans.Theory
import Hip.Trans.Property

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.List
import Data.Typeable as Typeable

import CoreSyn as C
import GHC
import Kind
import Name
import Outputable
import SrcLoc
import Type as GhcType
import Unique
import Id
import Var

import Control.Monad


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
  where err = error $ "Cannot translate QuickSpec's " ++ s
                   ++ " to Core representation! Debug the string marshallings"
                   ++ " with --db-str-marsh "

-- So far only works on arguments with monomorphic, non-exponential types
termsToProp :: StrMarsh -> Term -> Term -> Prop
termsToProp str_marsh e1 e2 = Prop
    { proplhs  = termToExpr str_marsh var_rename_map e1
    , proprhs  = termToExpr str_marsh var_rename_map e2
    , propVars = [ (setVarType v ty,ty)
                 | (x,v) <- var_rename
                 , let ty = typeRepToType str_marsh (symbolType x)
                 ]
    , propName = repr
    , propRepr = repr
    , propQSTerms = e1 :=: e2
    , propFunDeps = [ v
                    | c <- nub (funs e1 ++ funs e2)
                    , let (v,is_function_not_constructor) = lookupSym str_marsh c
                    , is_function_not_constructor
                    ]
    , propOops    = False
    }
  where
    repr           = show (e1 :=: e2)
    var_rename     = [ (x,setVarType v ty)
                     | x <- nub (vars e1 ++ vars e2)
                     , let ty = typeRepToType str_marsh (symbolType x)
                     | v <- varNames
                     ]
    var_rename_map = M.fromList var_rename

eqToProp :: StrMarsh -> Equation -> Prop
eqToProp str_marsh (t :=: u) = termsToProp str_marsh t u

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
