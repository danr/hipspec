{-# LANGUAGE DeriveDataTypeable #-}
module Hip.Trans.Core where

import Data.Data
import Data.Generics.Uniplate.Data
import Data.List (partition)
import Control.Arrow ((&&&))

type Name = String

data Decl = Func   { declName :: Name
                   , declArgs :: [Name]
                   , funcBody :: Body
                   }
          | Data   { declName :: Name
                   , declArgs :: [Name]
                   , dataCons :: [Cons] }
          | TyDecl { declName :: Name
                   , declType :: Type
                   }
  deriving(Eq,Ord,Data,Typeable)

data Cons = Cons { conName :: Name
                 , conArgs :: [Type]
                 }
  deriving(Eq,Ord,Data,Typeable)

data Body = Case { caseScrutinee :: Expr
                 , caseBranches :: [Branch]
                 }
          | Expr Expr
  deriving(Eq,Ord,Data,Typeable)

data Expr = App { exprName :: Name , exprArgs :: [Expr] }
          | Con { exprName :: Name , exprArgs :: [Expr] }
          | Var { exprName :: Name }
          | IsBottom Expr
          -- ^ For guards that evaluate to bottom
          | Expr ::: Type
          -- ^ Used in instantiating induction schemas
          --   (never else)
  deriving(Eq,Ord,Data,Typeable)

infix 7 :->

data Branch = (:->) { brPMG :: PMG , brExpr :: Expr }
  deriving(Eq,Ord,Data,Typeable)

-- Pattern + Maybe Guard
data PMG = NoGuard { pattern :: Pattern }
         | Guard   { pattern :: Pattern , guardExpr :: Expr }
  deriving(Eq,Ord,Data,Typeable)

data Pattern = PVar { patName :: Name }
             | PCon { patName :: Name , patArgs :: [Pattern] }
  deriving(Eq,Ord,Data,Typeable)

-- Cannot handle type var applications, as f in : (a -> b) -> f a -> f b
data Type = TyVar Name
          | TyApp [Type]
          | TyCon Name [Type]
  deriving(Eq,Ord,Data,Typeable)

-- Auxiliary functions

isTyVar :: Type -> Bool
isTyVar TyVar{} = True
isTyVar _       = False

-- | Modify the pattern of a PMG
modifyPattern :: (Pattern -> Pattern) -> PMG -> PMG
modifyPattern f (Guard p e) = Guard (f p) e
modifyPattern f (NoGuard p) = NoGuard (f p)

-- | Modify the guard of a PMG if it exists
modifyGuard :: (Expr -> Expr) -> PMG -> PMG
modifyGuard f (Guard p e) = Guard p (f e)
modifyGuard _ ng          = ng

-- | Declaration is a function declaration
funcDecl :: Decl -> Bool
funcDecl Func{} = True
funcDecl _      = False

-- | Declaration is a data declaration
dataDecl :: Decl -> Bool
dataDecl Data{} = True
dataDecl _      = False

typeDecl :: Decl -> Bool
typeDecl TyDecl{} = True
typeDecl _        = False

-- | Partition declarations into function-, data- and type declarations
partitionDecls :: [Decl] -> ([Decl],[Decl],[Decl])
partitionDecls ds =
   let (funs,rest)   = partition funcDecl ds
       (datas,types) = partition dataDecl rest
   in  (funs,datas,types)


conNameArity :: Decl -> [(Name,Int)]
conNameArity (Data _ _ cs) = map (\(Cons n as) -> (n,length as)) cs
conNameArity _             = error "conNameArity: Please report this error."

conTypes :: Decl -> [(Name,Type)]
conTypes (Data name vars cons) = map (conName &&& conType) cons
  where
    dataType = TyCon name (map TyVar vars)
    conType (Cons name [])  = dataType
    conType (Cons name tys) = TyApp (tys ++ [dataType])
conTypes _ = error "conTypes: Please report this error."

-- | The two kinds of patterns
varPat,conPat :: Pattern -> Bool
varPat PVar{} = True
varPat _      = False
conPat PCon{} = True
conPat _      = False

-- | Costructor pattern without arguments
con0Pat :: Pattern -> Bool
con0Pat (PCon _ []) = True
con0Pat _           = False

-- | With or without guard
guarded,notGuarded :: PMG -> Bool
guarded Guard{} = True
guarded _       = False
notGuarded = not . guarded

-- | Transforms applications to the function/constructor name with an
--   argument list.
app :: Expr -> Expr -> Expr
app (App n es) e = App n (es ++ [e])
app (Con n es) e = Con n (es ++ [e])
app (Var n)    e = App n [e]
app IsBottom{} _ = error "app on IsBottom"

infixl `app`

tapp :: Type -> Type -> Type
tapp t (TyApp []) = t
tapp t (TyApp ts) = TyApp (t:ts)
tapp t t2         = TyApp [t,t2]

tconapp :: Type -> Type -> Maybe Type
tconapp (TyCon n ts) t = Just (TyCon n (ts ++ [t]))
tconapp _            t = Nothing

infixr `tapp`

-- | Nullary constructor
con0 :: Name -> Expr
con0 n = Con n []

-- | Nullary constructor pattern
pcon0 :: Name -> Pattern
pcon0 n = PCon n []

-- | Nullary type constructor
tycon0 :: Name -> Type
tycon0 n = TyCon n []

-- | Which variables does a pattern bind?
patternBinds :: Pattern -> [Name]
patternBinds p = [ x | PCon x _ <- universe p ]

-- | Type variables in a type
tyVars :: Type -> [Name]
tyVars t = [ x | TyVar x <- universe t ]

-- | Substitution
subst :: Name -> Name -> Expr -> Expr
subst xold xnew = transform f
  where f (Var x)    | x == xold = Var xnew
        f (App x as) | x == xold = App xnew as
        f e = e

test :: Name -> Name -> Expr -> [Expr]
test xold xnew = transformM f
  where f e@(Var x)    | x == xold = [e,Var xnew]
        f e@(App x as) | x == xold = [e,App xnew as]
        f e = [e]

-- | Translate a pattern to an expression. This is needed to get the
--   more specific pattern for a branch.
patternToExpr :: Pattern -> Expr
patternToExpr (PVar x)    = Var x
patternToExpr (PCon p ps) = Con p (map patternToExpr ps)

-- | Substitute in a body
substBody :: Name -> Name -> Body -> Body
substBody xold xnew (Expr e) = Expr (subst xold xnew e)
substBody xold xnew (Case e brs) = Case (subst xold xnew e) $
                                      map (substBranch xold xnew) brs

-- | Substitute in a branch
substBranch :: Name -> Name -> Branch -> Branch
substBranch xold xnew b@(Guard p g :-> e)
  | xold `elem` patternBinds p = b
  | otherwise = Guard p (subst xold xnew g) :-> subst xold xnew e
substBranch xold xnew b@(NoGuard p :-> e)
  | xold `elem` patternBinds p = b
  | otherwise = NoGuard p :-> subst xold xnew e

-- | Substitute the function body
substFunDeclBody :: Name -> Name -> Decl -> Decl
substFunDeclBody xold xnew d = d { funcBody = substBody xold xnew (funcBody d) }

-- | Substitute a list of variables
substVars :: [(Name,Name)] -> Expr -> Expr
substVars ns e = foldr (\(x,x') -> subst x x') e ns

-- | Substitute a list of variables in the body
substVarsBody :: [(Name,Name)] -> Body -> Body
substVarsBody ns e = foldr (\(x,x') -> substBody x x') e ns

-- | Conrete types are types like Nat, Tree a, but not a or Nat -> Nat
concreteType :: Type -> Bool
concreteType TyCon{} = True
concreteType _       = False

-- | Strips an expression of its types
stripTypes :: Expr -> Expr
stripTypes = transform f
  where
    f (e ::: t) = e
    f e         = e

-- | The result of a type function
resType :: Type -> Type
resType t = case t of TyApp ts -> last ts
                      _        -> t

-- | Type of the arguments to a function
argsTypes :: Type -> [Type]
argsTypes t = case t of TyApp ts -> init ts
                        _        -> []

-- | Removes the type constructor if there is one. Used for removing Prop
unProp :: Type -> Type
unProp (TyCon _ [t]) = t
unProp t             = t

-- | Which arguments to this constructor are recursive?
--
--   For example, Branch :: Tree a -> a -> Tree a -> Tree a is
--   recursive in its first and third argument, as it is the same as
--   the resulting type, so the result of this function will be
--   [True,False,True]
recursiveArgs :: Type -> [Bool]
recursiveArgs (TyApp ts) = let resType = last ts
                           in  map (== resType) (init ts)
recursiveArgs _          = []

{-
 Given a function name and the matrix of patterns and expressions,
 returns a function which cases on the arguments and branches
 on the patterns and expressions

 f p11 p12 ... p1n | g1 = e1
 ...
 f pk1 pk2 ... pkn | gk = ek

   =>

 f u1 ... un = case Tn u1 .. un of
                   Tn p11 ... p1n | g1 -> e1
                   ...
                   Tn pk1 ... pkn | gk -> ek

 The corresponding function call is
 funcMatrix "f" [ ( [p11,...,p1n] , e1 ), ... , ([pk1,...,pkn] , ek) ]

-}
funcMatrix :: Name -> [([Pattern],Maybe Expr,Expr)] -> Decl
funcMatrix n [] = error "funcMatrix on empty matrix!"
funcMatrix n [(ps,Nothing,e)] | all varPat ps = Func n (map patName ps)
                                                       (Expr e)
funcMatrix n m@(mn:_) = Func n us $ Case (con (map Var us))
                                  [ guardMaybe ps mg :-> e | (ps,mg,e) <- m ]
  where fst3 (x,_,_) = x
        len = length (fst3 mn)
        us  = [ "u_" ++ show x | x <- [1..len] ]
        tup = 'T' : show len
        (con,pcon) = if len == 1 then (head,head)
                                 else (Con tup,PCon tup)
        guardMaybe :: [Pattern] -> Maybe Expr -> PMG
        guardMaybe ps (Just e) = Guard   (pcon ps) e
        guardMaybe ps Nothing  = NoGuard (pcon ps)

{-
   Expand a function definition with pattern matchings
   by prepending the pattern on the body case, or
   do the same as funcMatrix above.
-}
func :: Name -> [Pattern] -> Body -> Decl
func n ps b | all varPat ps || null ps = Func n (map patName ps) b
func n ps (Expr e)     = funcMatrix n [(ps,Nothing,e)]
func n ps (Case s brs) = Func n us $
                         Case (Con tup (s : map Var us))
                              [ modifyPattern (\p -> PCon tup (p:ps)) pmg :-> e
                              | pmg :-> e <- brs ]
  where len = length ps
        us  = [ "u_" ++ show x | x <- [1..len] ]
        tup = 'T' : show (len + 1)

