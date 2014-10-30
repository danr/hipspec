{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE PatternGuards,DeriveGeneric,StandaloneDeriving #-}
module HipSpec.Id where

import Name hiding (varName)
import OccName (occNameString)
-- import BasicTypes (TupleSort(..))
import PrelNames
import HipSpec.GHC.Utils
import Var (Var,varName,idDetails,TyVar,tyVarName)
import IdInfo (IdDetails(..))
import TyCon (tyConName,TyCon)
import DataCon (dataConName,DataCon)
import Data.Char (toUpper)

import qualified QuickSpec.Term as QS
import qualified QuickSpec.Type as QS
import qualified QuickSpec.Base as QS -- (prettyShow)

#ifdef SUPPORT_JSON
import Data.Aeson
#endif
import GHC.Generics
import PrimOp

import Data.Map (Map)
import qualified Data.Map as M

idFromPrimOp :: PrimOp -> Id
idFromPrimOp = GHCPrim

idFromName :: Name -> Id
idFromName nm
    | Just op <- M.lookup (nameOccName nm) primops = idFromPrimOp op
    | otherwise = GHCOrigin nm

primops :: Map OccName PrimOp
primops = M.fromList [(primOpOcc o,o) | o <- allThePrimOps]


idFromDataCon :: DataCon -> Id
idFromDataCon = idFromName . dataConName

idFromVar :: Var -> Id
idFromVar i = case idDetails i of
    DataConWorkId dc -> idFromDataCon dc
    DataConWrapId dc -> idFromDataCon dc
    _                -> idFromName (varName i)

idFromTyVar :: TyVar -> Id
idFromTyVar = idFromName . tyVarName

idFromTyCon :: TyCon -> Id
idFromTyCon = idFromName . tyConName

tryGetGHCName :: Id -> Maybe Name
tryGetGHCName (GHCOrigin nm) = Just nm
tryGetGHCName _              = Nothing

data Id
    = GHCOrigin Name
    | GHCPrim PrimOp
    | QSVariable QS.Variable
    | QSTyVar QS.TyVar
    | QSPropId Integer
    | Derived Derived Integer
    | Const Int Int
  deriving (Eq,Ord,Show,Generic)

instance Show Name where
    show nm = show (showOutputable nm)

deriving instance Show PrimOp
deriving instance Show PrimOpVecCat

data Derived
    = Id `LetFrom` Id
    | Lambda Id
    | Case Id
    | Eta
    | Skolem Id
    | TvSkolem Id
    | Unknown
    | GenTyVar
    | Id `Fix` BW
  deriving (Eq,Ord,Show,Generic)

-- we turn {f = .. f ..}
-- into    {fB = .. fW ..}
data BW = B | W
  deriving (Eq,Ord,Show,Generic)

#ifdef SUPPORT_JSON
instance ToJSON Id
instance ToJSON Derived
instance ToJSON BW

instance ToJSON QS.TyVar where toJSON _ = Null
instance ToJSON QS.Variable where toJSON _ = Null
instance ToJSON Name where toJSON _ = Null
#endif

mkLetFrom :: Id -> Integer -> Id -> Id
mkLetFrom x _ (Derived Unknown _) = x
mkLetFrom x i y                   = Derived (x `LetFrom` y) i

originalId :: Id -> String
originalId i = case i of
    GHCOrigin nm  -> getOccString nm
    GHCPrim op    -> show op -- "PRIM_" ++ occNameString (primOpOcc op)
    QSVariable v  -> QS.prettyShow v
    QSTyVar tv    -> QS.prettyShow tv
    Const 0 2     -> "const"
    Const i j     -> "const_" ++ show i ++ "_" ++ show j
    Derived d _   -> case d of
        _ `LetFrom` b -> originalId b ++ "_"
        Lambda a      -> originalId a ++ "_lambda"
        Case a        -> originalId a ++ "_case"
        Skolem a      -> originalId a
        TvSkolem a    -> map toUpper (originalId a)
        Eta           -> "x"
        Unknown       -> "u"
        GenTyVar      -> "a"
        f `Fix` _bw   -> "{" ++ originalId f ++ "}"

-- | Pretty prints an Id.
--   Not necessarily to a unique String, the Renamer takes care of proper
--   disabiguation.
ppId :: Id -> String
ppId i = case i of
    GHCOrigin nm  -> ppName nm
    GHCPrim op    -> show op
    QSVariable v  -> QS.prettyShow v
    QSTyVar tv    -> QS.prettyShow tv
    Derived d x   -> ppDerived x d
    Const 0 2     -> "const"
    Const i j     -> "const_" ++ show i ++ "_" ++ show j

ppDerived :: Integer -> Derived -> String
ppDerived i d = case d of
    f `LetFrom` g -> (case ppId g of { [] -> ""; s -> s ++ "_" }) ++ ppId f
    Lambda f      -> "lam_" ++ ppId f
    Case f        -> "case_" ++ ppId f
    Eta           -> "eta"
    Skolem x      -> ppId x
    TvSkolem x    -> map toUpper (ppId x)
    GenTyVar      -> [['a'..'z'] !! (fromInteger i `mod` 26)]
    Unknown       -> "unknown"
    f `Fix` bw    -> ppId f ++ show bw

ppName :: Name -> String
ppName nm -- = getOccString nm {- ++ '_': showOutputable (getUnique nm) -}
    | k == listTyConKey      = "List"
    | k == nilDataConKey     = "Nil"
    | k == consDataConKey    = "Cons"
    | k == unitTyConKey      = "UnitTyCon"
    | k == genUnitDataConKey = "Unit"
    | otherwise = case getOccString nm of
        "(,)"  -> "Tup"
        "(,,)" -> "Trip"
        "+"   -> "plus"
        "-"   -> "minus"
        "/"   -> "div"
        "*"   -> "mult"
        "^"   -> "pow"
        "++"  -> "append"
        ">>=" -> "bind"
        "=<<" -> "dnib"
        ">=>" -> "dot_monadic"
        "<=<" -> "monadic_dot"
        "<*>" -> "ap"
        "<$>" -> "fmap"
        ">>"  -> "then"
        "||"  -> "or"
        "&&"  -> "and"
        "."   -> "dot"
        "=="  -> "equal"
        "/="  -> "unequal"
        ">"   -> "gt"
        ">="  -> "ge"
        "<"   -> "lt"
        "<="  -> "le"
        "$"   -> "apply"
        "!!"  -> "index"
        "\\\\" -> "difference"
        s     -> s
  where
    k = getUnique nm

