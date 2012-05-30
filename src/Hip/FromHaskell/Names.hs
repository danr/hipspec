module Hip.FromHaskell.Names where

import Hip.FromHaskell.Monad
import qualified Hip.Trans.Core as C
import Hip.Trans.Core (Name,tapp,tconapp,tycon0)
import qualified Language.Haskell.Exts as H
import Language.Haskell.Exts hiding (Name,name)
import Control.Monad
import Control.Applicative

-- Names ----------------------------------------------------------------------
unitName,nilName,consName,listTypeName :: Name
unitName = "()"
nilName  = "[]"
consName = ":"
listTypeName = "[]"

tupleName :: Int -> Name
tupleName n = 'T':show n

-- Extracting names -----------------------------------------------------------

matchName :: Match -> H.Name
matchName (Match _ name _ _ _ _) = name

fromName :: H.Name -> Name
fromName (Ident s)  = s
fromName (Symbol s) = s

fromQName :: QName -> FH Name
fromQName q@(Qual _modulename name) = do
  warn $ "No handling for qualifed names: " ++ prettyPrint q
  return (fromName name)
fromQName (UnQual name) = return (fromName name)
fromQName (Special special) = fromSpecial special

fromSpecial :: SpecialCon -> FH Name
fromSpecial UnitCon = regData unitName >> return unitName
fromSpecial ListCon = regData listTypeName >> return nilName
fromSpecial FunCon  = warn "Using FunCon" >> return "->"
fromSpecial (TupleCon b n) = do
  when (b == Unboxed) $ warn "No handling of unboxed tuples"
  regData (tupleName n)
  return (tupleName n)
fromSpecial Cons    = regData listTypeName >> return ":"
fromSpecial UnboxedSingleCon = do
  fatal "No handling of unboxed singleton constructor"

fromQualConDecl :: QualConDecl -> FH C.Cons
fromQualConDecl (QualConDecl _loc _tyvars _cxtx condecl) = fromConDecl condecl

fromConDecl :: ConDecl -> FH C.Cons
fromConDecl c = case c of
  ConDecl name bangts ->
    C.Cons (fromName name) <$> mapM fromBangType bangts
  InfixConDecl bangt1 name bangt2 ->
    C.Cons (fromName name) <$> mapM fromBangType [bangt1,bangt2]
  RecDecl name namedbangtypes -> do
      warn $ "not creating projection declarations (" ++ fromName name ++ ")"
      C.Cons (fromName name) <$> mapM (fromBangType . snd) namedbangtypes

fromBangType :: BangType -> FH C.Type
fromBangType (UnBangedTy t) = fromType t
fromBangType bt@(BangedTy t) = do warn $ "Ignoring bang on " ++ prettyPrint bt
                                  fromType t
fromBangType bt@(UnpackedTy t) = do warn $ "Ignoring unpacked on " ++ prettyPrint bt
                                    fromType t

fromType :: Type -> FH C.Type
fromType ty = case ty of
  TyFun t1 t2 -> tapp <$> fromType t1 <*> fromType t2
  TyApp t1 t2 -> do r <- tconapp <$> fromType t1 <*> fromType t2
                    case r of
                       Just t -> return t
                       Nothing -> fatal $ "Cannot handle type application" ++ prettyPrint ty
  TyVar n -> return $ C.TyVar (fromName n)
  TyList t -> C.TyCon listTypeName . return <$> fromType t
  TyTuple b ts -> C.TyCon (tupleName (length ts)) <$> mapM fromType ts
  TyCon qn -> tycon0 <$> fromQName qn
  TyKind t k -> do warn $ "Ignoring kind on " ++ prettyPrint ty
                   fromType t
  TyForall{} -> fatal $ "Cannot handle forall: " ++ prettyPrint ty
  TyParen t -> fromType t
  TyInfix t1 qn t2 -> do t1' <- fromType t1
                         n <- fromQName qn
                         t2' <- fromType t2
                         return (C.TyCon n [t1',t2'])

fromTyVarBind :: TyVarBind -> FH Name
fromTyVarBind t@(KindedVar n k) = do warn $ "Ignoring kind on " ++ prettyPrint t
                                     return (fromName n)
fromTyVarBind (UnkindedVar n) = return (fromName n)