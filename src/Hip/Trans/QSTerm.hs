{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards #-}
{-|

   Translating from QuickSpec -> Core

-}
module Hip.Trans.QSTerm where


import Test.QuickSpec.Term
import qualified Test.QuickSpec.Term as T

import Hip.Annotations
import Hip.Trans.Theory

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

type Equation = (Term Symbol,Term Symbol)

typeRepToType :: ANNs -> TypeRep -> Type
typeRepToType (_,strToTyCon) = go
  where
    go :: TypeRep -> Type
    go t | [(ta,tb)] <- funTypes [t]   = go ta `GhcType.mkFunTy` go tb
    go t = let (ty_con,ts) = Typeable.splitTyConApp t
               _tr r = tyConName ty_con ++ " ~> " ++ showSDoc (pprSourceTyCon r)
           in  fromMaybe a
                (fmap (\r -> {- trace (tr r) -} r `GhcType.mkTyConApp` map go ts)
                      (M.lookup (tyConName ty_con) strToTyCon))
    a :: Type
    a = mkTyVarTy $ mkTyVar
                (mkInternalName (mkUnique 'j' 1337)
                                (mkOccName tvName "a")
                                wiredInSrcSpan) anyKind

termToExpr :: ANNs -> Map Symbol Var -> Term Symbol -> CoreExpr
termToExpr anns var_rename_map = go
  where
    go t = case t of
        T.App e1 e2 -> go e1 `C.App` go e2
        T.Var s   -> C.Var (fromMaybe (err s) (M.lookup s var_rename_map))
        T.Const s -> C.Var (fst $ lookupSym anns s)

    err (name -> s) = error $ "QuickSpec's " ++ s ++ " never got a variable"

lookupSym :: ANNs -> Symbol -> (Var,Bool)
lookupSym (strToVar,_) (name -> s) = fromMaybe err (M.lookup s strToVar)
  where err = error $ "Cannot translate QuickSpec's " ++ s
                   ++ " to Core representation!"

-- So far only works on arguments with monomorphic, non-exponential types
termsToProp :: ANNs -> Term Symbol -> Term Symbol -> Prop
termsToProp anns e1 e2 = Prop
    { proplhs  = termToExpr anns var_rename_map e1
    , proprhs  = termToExpr anns var_rename_map e2
    , propVars = [ (v,typeRepToType anns (symbolType x))
                 | (x,v) <- var_rename ]
    , propName = repr
    , propRepr = repr
    , propQSTerms = (e1,e2)
    , propFunDeps = [ v
                    | c <- nub (constants e1 ++ constants e2)
                    , let (v,is_function_not_constructor) = lookupSym anns c
                    , is_function_not_constructor
                    ]
    , propOops    = False
    }
  where
    repr           = showEq (e1,e2)
    var_rename     = [ (x,v)
                     | x <- nub (vars e1 ++ vars e2)
                     | v <- varNames ]
    var_rename_map = M.fromList var_rename

showEq :: Equation -> String
showEq (e1,e2) = show e1 ++ " = " ++ show e2

csv :: [String] -> String
csv = intercalate ", "

-- | A bunch of _local_ variable names to quantify over
varNames :: [Var]
varNames =
   [ mkLocalId
       (mkInternalName (mkUnique '!' i) (mkOccName Name.varName n) wiredInSrcSpan)
       (error "QSTerm.varNames: type")
   | i <- [0..]
   | n <- [1..] >>= flip replicateM "xyzwvu"
   ]
