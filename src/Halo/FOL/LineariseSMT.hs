-- Linearises (pretty prints) our FOL representation into SMT
module Halo.FOL.LineariseSMT (linSMT) where

import Outputable hiding (quote)

import Data.List

import Var
import TysPrim
import Type
import TysWiredIn
import DataCon
import Name hiding (varName)

import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Operations
import Halo.FOL.Abstract

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe

-- | Linearise a set of clauses to a String
linSMT :: [Clause'] -> String
linSMT = (++ "\n") . showSDoc . linClauses

-- | Linearise a sort declaration
--   We will only declare the sort D of our domain
linDeclSort :: SDoc -> SDoc
linDeclSort s = parens (text "declare-sort" <+> s)

-- | Linearise a function declaration
--   The argument list is empty if this is a constant
linDeclFun :: SDoc -> [SDoc] -> SDoc -> SDoc
linDeclFun name args res =
    parens (text "declare-fun" <+> name <+> parens (sep args) <+> res)

-- | Linearise the set of clauses
linClauses :: [Clause'] -> SDoc
linClauses cls = vcat $ concat
    [ [parens (text "set-option :print-success false")]
    , [linDeclSort linDomain]
    , min_decl
    , minrec_decl
    , cf_decl
    , app_decl
    , constant_decls
    , function_decls
    , projection_decls
    , lift_bool_defn
    , map linClause cls
    , [parens (text "check-sat")]
    ]
  where
    app_decl
        = [ linDeclFun linApp [linDomain,linDomain] linDomain | any appUsed cls ]

    unary_pred p g = [ linDeclFun p [linDomain] linBool | any g cls ]

    min_decl       = unary_pred linMin    minUsed
    minrec_decl    = unary_pred linMinRec minRecUsed
    cf_decl        = unary_pred linCF     cfUsed

    constant c     = linDeclFun c [] linDomain
    constants f ln = map (constant . ln) . S.toList . S.unions . map f $ cls

    constant_decls = constants ptrsUsed linPtr ++ constants skolemsUsed linSkolem

    function c arg_tys = linDeclFun c (map linType arg_tys) linDomain
    functions f linF = map (\(c,i) -> function (linF c) (fun_arg_tys c i))
                     . S.toList . S.unions . map f $ cls

    lift_bool_defn =
        [ linLiftBoolDefn | S.member LiftBool . S.unions . map primsUsed $ cls ]

    -- I# should be Int# -> D
    fun_arg_tys :: Var -> Int -> [Type]
    fun_arg_tys f i = take i (ts ++ repeat anyTy)
      where (ts,_) = splitFunTys (repType (varType f))

    function_decls = functions funsUsed linFun ++ functions consUsed linCtor

    projection_decls =
        [ linDeclFun (linProj p c) [linDomain] (linType ty)
        | (c,i) <- S.toList . S.unions . map consUsed $ cls
        , let (tys,_) = splitFunTys (repType (varType c))
        , (p,ty) <- zip [0..i-1] (tys ++ repeat anyTy)
        -- sel_0_I# should be D -> Int#
        ]

-- | Linearises a clause
linClause :: Clause' -> SDoc
linClause (Comment s)
    = text ("\n" ++ intercalate "\n" (map ("; " ++) (lines s)))
linClause (Clause cl_name cl_type cl_formula)
    = ((cl_name /= "x") ? ((text $ "; " ++ cl_name ++ "\n") <>))
    $ parens $
        (text "assert") <+>
        (linForm $ (cl_type == Conjecture ? neg) cl_formula)

-- | Linearise a formula.
--   Second argument is if it should be enclosed in parentheses.
linForm :: Formula' -> SDoc
linForm form = parens $ case form of
    Equal   t1 t2    -> linEqOp equals t1 t2
    Unequal t1 t2    -> linEqOp (text "distinct") t1 t2
    And fs           -> linBinOp (text "and") fs
    Or  fs           -> linBinOp (text "or") fs
    Implies f1 f2    -> linBinOp darrow [f1,f2]
    Forall qs f      -> linQuant (text "forall") qs f
    Exists qs f      -> linQuant (text "exists") qs f
    Pred p tms       -> linTrue $ linPred p <+> sep (map linTerm tms)
    Neg (Pred p tms) -> linFalse $ linPred p <+>  sep (map linTerm tms)
    Neg f            -> text "not" <+> linForm f

linPred :: Pred -> SDoc
linPred Min    = linMin
linPred MinRec = linMinRec
linPred CF     = linCF
linPred IsType = linIsType

linTrue :: SDoc -> SDoc
linTrue t = equals <+> text "true" <+> parens t

linFalse :: SDoc -> SDoc
linFalse t = equals <+> text "false" <+> parens t

-- | Linearise the equality operations: =, !=
linEqOp :: SDoc -> Term' -> Term' -> SDoc
linEqOp op t1 t2 = op <+> linTerm t1 <+> linTerm t2

-- | Linearise binary operations: or, and, =>
linBinOp :: SDoc -> [Formula'] -> SDoc
linBinOp op fs = op <+> sep (map linForm fs)

-- | Linearise quantifiers: ! [..] :, ? [..] :
--   op list should _not_ be empty
linQuant :: SDoc -> [Var] -> Formula' -> SDoc
linQuant op qs f = hang
    (op <+> parens (sep (map (linQuantBinder) qs))) 4
    (linForm f)

-- | Linearises a quantifier binder, such as (x D) or (y Int)
linQuantBinder :: Var -> SDoc
linQuantBinder v = parens (linQuantVar v <+> linType (varType v))

-- | Linearises a type, D or Int
linType :: Type -> SDoc
linType t | t `eqType` intPrimTy = linInt
          | otherwise            = linDomain

-- | Linearise a term
--   The way to carry out most of the work is determined in the Style.
linTerm :: Term' -> SDoc
linTerm (Skolem a) = linSkolem a
linTerm tm = case tm of
    Fun a []    -> linFun a
    Fun a tms   -> parens $ linFun a <+> linTerms tms
    Ctor a []   -> linCtor a
    Ctor a tms  -> parens $ linCtor a <+> linTerms tms
    Skolem a    -> linSkolem a
    App t1 t2   -> parens $ linApp <+> linTerms [t1,t2]
    Proj i c t  -> parens $ linProj i c <+> linTerm t
    Ptr a       -> linPtr a
    QVar a      -> linQuantVar a
    Prim p tms  -> parens $ linPrim p <+> linTerms tms
    Lit i       -> integer i
  where
    linTerms = sep . map linTerm

-- | Our domain D
linDomain :: SDoc
linDomain = char 'D'

-- | Integers
linInt    :: SDoc
linInt    = text "Int"

-- | For predicates, the sort of booleans is used
linBool   :: SDoc
linBool   = text "Bool"

-- | Short representation of a Var to String
showVar :: Var -> String
showVar v = (++ "_" ++ show (varUnique v))
          . escape . showSDocOneLine . ppr . maybeLocaliseName . varName $ v
  where
    maybeLocaliseName n
        | isSystemName n = n
        | otherwise      = localiseName n

-- | Pretty printing functions and variables
linFun      :: Var -> SDoc
linFun      = text . ("f_" ++) . showVar

-- | Pretty printing constructors
linCtor     :: Var -> SDoc
linCtor     = text . ("c_" ++) . showVar

-- | Pretty printing Skolemised variables
linSkolem   :: Var -> SDoc
linSkolem   = text . ("a_" ++) . showVar

-- | Quantified variables
linQuantVar :: Var -> SDoc
linQuantVar = text . ("q_" ++) . showVar

-- | The app/@ symbol
linApp      :: SDoc
linApp      = text "app"

-- | The min symbol
linMin      :: SDoc
linMin      = text "min"

-- | The minrec symbol
linMinRec   :: SDoc
linMinRec   = text "minrec"

-- | The CF symbol
linCF       :: SDoc
linCF       = text "cf"

-- | The IsType symbol
linIsType   :: SDoc
linIsType   = text "type"

-- | Projections
linProj     :: Int -> Var -> SDoc
linProj i   = text . (("s_" ++ show i ++ "_") ++) . showVar

-- | Pointers
linPtr      :: Var -> SDoc
linPtr      = text . ("p_" ++) . showVar

-- | Escaping
escape :: String -> String
escape = concatMap (\c -> fromMaybe [c] (M.lookup c escapes))

-- | Some kind of z-encoding escaping
escapes :: Map Char String
escapes = M.fromList $ map (uncurry (flip (,)))
    [ ("za",'@')
    , ("z1",'(')
    , ("z2",')')
    , ("zB",'}')
    , ("zC",'%')
    , ("zG",'>')
    , ("zH",'#')
    , ("zL",'<')
    , ("zR",'{')
    , ("zT",'^')
    , ("zV",'\\')
    , ("z_",'\'')
    , ("zb",'!')
    , ("zc",':')
    , ("zd",'$')
    , ("zh",'-')
    , ("zi",'|')
    , ("zl",']')
    , ("zm",',')
    , ("zn",'&')
    , ("zo",'.')
    , ("zp",'+')
    , ("zq",'?')
    , ("zr",'[')
    , ("zs",'*')
    , ("zt",'~')
    , ("zv",'/')
    , ("zz",'z')
    , ("_equals_",'=')
    , ("_",' ')
    ]

linPrim :: Prim -> SDoc
linPrim p = case p of
    Add -> char '+'
    Sub -> char '-'
    Mul -> char '*'
    Eq  -> char '='
    Ne  -> text "!=" -- will this work?
    Lt  -> char '<'
    Le  -> text "<="
    Ge  -> text ">="
    Gt  -> char '>'
    LiftBool -> linLiftBool

linLiftBool :: SDoc
linLiftBool = text "lift_bool"

linLiftBoolDefn :: SDoc
linLiftBoolDefn = vcat $
    linDeclFun linLiftBool [linBool] linDomain :
    [ parens $ text "assert" <+>
        parens (equals <+> parens (linLiftBool <+> text in_bool)
                       <+> in_domain)
    | (in_bool,in_domain) <-
        [("true",linCtor (dataConWorkId trueDataCon))
        ,("false",linCtor (dataConWorkId falseDataCon))
        ]
    ]

{-
primType :: Prim -> ([SDoc],SDoc)
primType p = case p of
    Add      -> int_int_int
    Sub      -> int_int_int
    Mul      -> int_int_int
    Eq       -> int_int_bool
    Ne       -> int_int_bool
    Lt       -> int_int_bool
    Le       -> int_int_bool
    Ge       -> int_int_bool
    Gt       -> int_int_bool
    LiftBool -> ([linBool],linDomain)
  where
    int_int_int  = ([linInt,linInt],linInt)
    int_int_bool = ([linInt,linInt],linBool)
-}
