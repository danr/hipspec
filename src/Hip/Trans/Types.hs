{-# LANGUAGE PatternGuards #-}
module Hip.Trans.Types
       (finiteTy,keep,
        anyTypeAxiom,
        typeGuard,typeGuards,
        infDomainAxiom,
        genTypePred)
       where

import Hip.Trans.Core
import Hip.Trans.Pretty
import Hip.Trans.ParserInternals
import Hip.Trans.TyEnv
import Hip.Trans.Names

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

import Data.Char

import Control.Applicative
import Control.Monad

-- | Is a constructor with a type finite?
finiteCon :: TyEnv -> [Type] -> Type -> Bool
finiteCon env tys t = not (any (`elem` tys) (argsTypes t))
                   && all (finiteTypeMut env tys) (argsTypes t)

-- | Is this type finite?
--
--   True  : Bool, (Bool,Bool), Ordering, Unit
--   False : a, [a], (a,Bool)
finiteTy :: TyEnv -> Type -> Bool
finiteTy _ (TyCon "Int" []) = False
finiteTy env ty = finiteTypeMut env [] ty

finiteTypeMut env tys ty@TyCon{} = case instantiate env ty of
    Just cons -> all (finiteCon env (ty:tys) . snd) cons
    Nothing   -> error $ "finiteTypeMut: " ++ show ty
finiteTypeMut _ _ _ = False -- Type variable or function space

-- | Should this type be kept? In other words, does it  contain
--   any subparts that are finite?
--
--   True  : Bool, [Bool], (Bool,a), [(Nat,Bool)]
--   False : [a], Nat
keep :: TyEnv -> Type -> Bool
keep env ty@(TyCon _ ts) = finiteTy env ty || any (keep env) ts
keep env _               = False

{-
testTypes = map parseType
   [ "Bool"
   , "Tree Bool"
   , "Tree a"
   , "List Bool"
   , "Unit"
   , "Maybe Bool"
   , "WrapList Bool"
   , "Nat"
   , "Z"
   , "Tup Bool Bool"
   , "Tup Unit Bool"
   , "Tup a Bool"
   , "Tup Bool (List a)"
   , "Either Bool Unit"
   , "Either Unit (List Unit)"
   , "Tup (Tup (Tup Bool Bool) (Either Bool Bool)) (Either Unit Bool)"
   , "Tup (Tup (Tup Bool Nat) (Either Bool Bool)) (Either Unit Bool)"
   ]

testFiniteTy,testKeep :: [(TypeName,Bool)]
testFiniteTy = map ((,) <$> show <*> finiteTy testEnv) testTypes
testKeep     = map ((,) <$> show <*> keep testEnv) testTypes
-}

-- | Generates the type predicate for a type
--
--   Example
--
--     Ty([a],[])
--     Ty([a],x:xs) <-> (Ty(a,x) /\ Ty([a],xs))
--
--     Ty((a,b),(x,y)) <-> (Ty(a,x) /\ Ty(b,y))
genTypePred :: TyEnv -> Type -> T.Decl
genTypePred env ty@(TyCon n as) = case instantiate env ty of
   Just cons -> genPred ty cons
   Nothing   -> error $ "genTypePred, not found: " ++ show ty
genTypePred env ty = error $ "genTypePred, not on a type constructor: " ++ show ty

genPred :: Type -> [(Name,Type)] -> T.Decl
genPred ty cons = Axiom "ty" (forall' (x : map quantName (tyVars ty))
                                      (rootFormula <=>
                                        foldl1 (\/) (map (uncurry genPredCon) cons)))
  where
     x  = VarName "R"
     xv = T.Var x

     rootFormula = tyRel (genType (resType ty)) xv

     genPredCon :: ConName -> Type -> T.Formula
     genPredCon con_name ty =
           foldl (/\) (xv === simpProjCon con_name xv con_name (length typedvars))
                       (map (\(v,t) -> tyRel (genType t) v) typedvars)
       where
         typedvars = [ proj con_name i xv | i <- [0..] ] `zip` argsTypes ty


infDomainAxiom :: TyEnv -> Type -> Maybe T.Decl
infDomainAxiom env ty
  | not (finiteTy env ty), Just cons <- instantiate env ty =
     Just (Axiom "inf" (forall' [x] (foldr1 (\/) (map (uncurry gen) cons))))
       where
         x  = VarName "X"
         xv = T.Var x

         rootFormula = tyRel (genType (resType ty)) xv

         gen :: ConName -> Type -> T.Formula
         gen con_name ty = xv === simpProjCon con_name xv con_name (length (argsTypes ty))
infDomainAxiom env ty = Nothing

genType :: Type -> T.Term
genType (TyVar v)    = T.Var (quantName v)
genType (TyCon n ts) = Fun (FunName ("t_" ++ n)) (map genType ts)
genType t@TyApp{}    = error $ "genType on function space: " ++ show t

anyTypeAxiom :: T.Decl
anyTypeAxiom = Axiom "anytype" $ forall' [x] (tyRel anyType xv)
  where
    x  = VarName "X"
    xv = T.Var x

typeGuard :: TyEnv -> T.Term -> Type -> T.Formula -> T.Formula
typeGuard env tm ty phi | keep env ty = tyRel (genType (instAny env ty)) tm ==> phi
typeGuard env tm ty phi               = phi

typeGuards :: TyEnv -> [(T.Term,Type)] -> T.Formula -> T.Formula
typeGuards env tytms phi = case filter (keep env . snd) tytms of
    []       -> phi
    finTyTms -> foldr1 (/\) tyRels ==> phi
      where tyRels = (map (\(tm,ty) -> tyRel (genType (instAny env ty)) tm) finTyTms)

instAny :: TyEnv -> Type -> Type
instAny env t | not (keep env t) = TyVar anyTypeName
instAny env (TyCon n ts)         = TyCon n [ if isTyVar t then TyVar anyTypeName
                                                          else instAny env t
                                           | t <- ts ]


anyTypeName :: Name
anyTypeName = "Any-Type"

anyType :: T.Term
anyType = Fun (FunName anyTypeName) []

tyRel :: T.Term -> T.Term -> T.Formula
tyRel t1 t2 = Rel (RelName "ty") [t1,t2]

-- | A list of nice variable names
varNames :: [String]
varNames = [1..] >>= flip replicateM "XYZWVU"

-- | Make a number of new variable names
makeVarNames :: Int -> [T.VarName]
makeVarNames n = take n (map VarName varNames)

quantName :: Name -> T.VarName
quantName = VarName . map toUpper

