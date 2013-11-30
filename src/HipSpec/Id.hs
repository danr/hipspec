module HipSpec.Id where

import Name hiding (varName)
import BasicTypes (TupleSort(..))
import PrelNames
import HipSpec.GHC.Utils
import Var (Var,varName,idDetails,TyVar,tyVarName)
import IdInfo (IdDetails(..))
import TyCon (tyConName,TyCon)
import DataCon (dataConName,DataCon)

idFromName :: Name -> Id
idFromName = GHCOrigin

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


data Id
    = GHCOrigin Name
    | Derived Derived Integer
  deriving (Eq,Ord)

instance Show Id where
    show (GHCOrigin nm)  = showOutputable nm ++ "_" ++ showOutputable (getUnique nm)
    show (Derived d i)   = show i ++ "_" ++ show d

data Derived
    = Id `LetFrom` Id
    | Lambda Id
    | Case Id
    | Eta
  deriving (Eq,Ord)

instance Show Derived where
    show (f `LetFrom` g) = "let_" ++ show f ++ "_from_" ++ show g ++ "_endlet"
    show (Lambda f)      = "lam_" ++ show f ++ "_endlam"
    show (Case f)        = "case_" ++ show f ++ "_endcase"
    show Eta             = "eta"

-- | Pretty prints an Id.
--   Not necessarily to a unique String, the Renamer takes care of proper
--   disabiguation.
ppId :: Id -> String
ppId i = case i of
    GHCOrigin nm  -> ppName nm
    Derived d _   -> ppDerived d

ppDerived :: Derived -> String
ppDerived d = case d of
    f `LetFrom` g -> ppId f ++ "_" ++ ppId g
    Lambda f      -> "lam_" ++ ppId f
    Case f        -> "case_" ++ ppId f
    Eta           -> "eta"

ppName :: Name -> String
ppName nm -- = getOccString nm {- ++ '_': showOutputable (getUnique nm) -}
    | k == listTyConKey      = "List"
    | k == nilDataConKey     = "Nil"
    | k == consDataConKey    = "Cons"
    | k == unitTyConKey      = "UnitTyCon"
    | k == genUnitDataConKey = "Unit"
    | Just (ns, ts, n) <- isTupleOcc_maybe (getOccName nm) = name_tuple ns ts n
    | otherwise = case getOccString nm of
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

    name_tuple ns ts n = pre ++ mid ++ show n
      where
        pre | ns == tcName   = "T"
            | ns == dataName = "t"
            | otherwise      = portableShowSDoc (pprNameSpace ns)

        mid = case ts of
            BoxedTuple   -> ""
            UnboxedTuple -> "u"
            _            -> "unknown_tuple"

{-
renameCls :: [Clause LogicId] -> [Clause String]
renameCls = runRenameM (zencode . polyname) altErgoKeywords . mapM rename
-}

altErgoKeywords :: [String]
altErgoKeywords =
    [ "ac"
    , "and"
    , "axiom"
    , "inversion"
    , "bitv"
    , "bool"
    , "check"
    , "cut"
    , "distinct"
    , "else"
    , "exists"
    , "false"
    , "forall"
    , "function"
    , "goal"
    , "if"
    , "in"
    , "include"
    , "int"
    , "let"
    , "logic"
    , "not"
    , "or"
    , "predicate"
    , "prop"
    , "real"
    , "rewriting"
    , "then"
    , "true"
    , "type"
    , "unit"
    , "void"
    , "with"
    ]

