-- Linearises (pretty prints) our FOL representation into SMT
module Halo.FOL.LineariseSMT (linSMT) where

import Outputable hiding (quote)

import Data.List

import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Operations
import Halo.FOL.Abstract

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe

-- | Linearise a set of clauses to a String
linSMT :: [StrClause] -> String
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
linClauses :: [StrClause] -> SDoc
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

    function c i   = linDeclFun c (replicate i linDomain) linDomain
    functions f ln = map (\(c,i) -> function (ln c) i)
                   . S.toList . S.unions . map f $ cls

    function_decls = functions funsUsed linFun ++ functions consUsed linCtor

    projection_decls = [ linDeclFun (linProj p c) [linDomain] linDomain
                       | (c,i) <- S.toList . S.unions . map consUsed $ cls
                       , p <- [0..i-1]
                       ]

-- | Linearises a clause
linClause :: StrClause -> SDoc
linClause (Comment s)
    = text ("\n" ++ intercalate "\n" (map ("; " ++) (lines s)))
linClause (Clause cl_name cl_type cl_formula)
    = ((cl_name /= "x") ? ((text $ "; " ++ cl_name ++ "\n") <>))
    $ parens $
        (text "assert") <+>
        (linForm $ (cl_type == Conjecture ? neg) cl_formula)

-- | Linearise a formula.
--   Second argument is if it should be enclosed in parentheses.
linForm :: StrFormula -> SDoc
linForm form = parens $ case form of
    Equal   t1 t2      -> linEqOp equals t1 t2
    Unequal t1 t2      -> linEqOp (text "distinct") t1 t2
    And fs             -> linBinOp (text "and") fs
    Or  fs             -> linBinOp (text "or") fs
    Implies f1 f2      -> linBinOp darrow [f1,f2]
    Forall qs f        -> linQuant (text "forall") qs f
    Exists qs f        -> linQuant (text "exists") qs f
    Min tm             -> linTrue $ linMin <+> linTerm tm
    MinRec tm          -> linTrue $ linMinRec <+> linTerm tm
    CF tm              -> linTrue $ linCF <+> linTerm tm
    IsType t1 t2       -> linTrue $ linEqOp linIsType t1 t2
    Neg (Min tm)       -> linFalse $ linMin <+> linTerm tm
    Neg (MinRec tm)    -> linFalse $ linMinRec <+> linTerm tm
    Neg (CF tm)        -> linFalse $ linCF <+> linTerm tm
    Neg (IsType t1 t2) -> linFalse $ linEqOp linIsType t1 t2
    Neg f              -> text "not" <+> linForm f

linTrue :: SDoc -> SDoc
linTrue t = equals <+> text "true" <+> parens t

linFalse :: SDoc -> SDoc
linFalse t = equals <+> text "false" <+> parens t

-- | Linearise the equality operations: =, !=
linEqOp :: SDoc -> StrTerm -> StrTerm -> SDoc
linEqOp op t1 t2 = op <+> linTerm t1 <+> linTerm t2

-- | Linearise binary operations: or, and, =>
linBinOp :: SDoc -> [StrFormula] -> SDoc
linBinOp op fs = op <+> sep (map linForm fs)

-- | Linearise quantifiers: ! [..] :, ? [..] :
--   op list should _not_ be empty
linQuant :: SDoc -> [String] -> StrFormula -> SDoc
linQuant op qs f = hang
    (op <+> parens (sep (map (parens . (<+> text "D") . linQVar) qs))) 4
    (linForm f)

-- | Linearise a term
--   The way to carry out most of the work is determined in the Style.
linTerm :: StrTerm -> SDoc
linTerm (Skolem a) = linSkolem a
linTerm tm = case tm of
    Fun a []    -> linFun a
    Fun a tms   -> parens $ linFun a <+> sep (map linTerm tms)
    Ctor a []   -> linCtor a
    Ctor a tms  -> parens $ linCtor a <+> sep (map linTerm tms)
    Skolem a    -> linSkolem a
    App t1 t2   -> parens $ linApp <+> sep (map linTerm [t1,t2])
    Proj i c t  -> parens $ linProj i c <+> linTerm t
    Ptr a       -> linPtr a
    QVar a      -> linQVar a

-- | Our domain D
linDomain :: SDoc
linDomain = char 'D'

-- | For predicates, the sort of booleans is used
linBool :: SDoc
linBool = text "Bool"

-- | Pretty printing functions and variables
linFun      :: String -> SDoc
linFun      = text . escape . ("f_" ++)

-- | Pretty printing constructors
linCtor     :: String -> SDoc
linCtor     = text . escape . ("c_" ++)

-- | Pretty printing Skolemised variables
linSkolem   :: String -> SDoc
linSkolem   = text . escape . ("a_" ++)

-- | Quantified variables
linQVar     :: String -> SDoc
linQVar     = text . escape . ("q_" ++)

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
linProj     :: Int -> String -> SDoc
linProj     = \i n -> text (escape ("p_" ++ show i ++ "_" ++ n))

-- | Pointers
linPtr      :: String -> SDoc
linPtr      = text . escape . ("ptr_" ++)

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
