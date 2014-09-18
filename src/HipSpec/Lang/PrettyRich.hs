{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on whether to print
--   types of variables.
module HipSpec.Lang.PrettyRich where

import Text.PrettyPrint

import HipSpec.Lang.Rich
import HipSpec.Lang.PrettyUtils
import HipSpec.Lang.Type

data WhetherTo a = Do a | Don't

data ShowTypes = ShowTypes
data ShowGblStar = ShowGblStar
data ShowTypeArgs = ShowTypeArgs

data PPOpt = PPOpt
  { pp_types     :: WhetherTo ShowTypes
  , pp_gbl_star  :: WhetherTo ShowGblStar
  , pp_type_args :: WhetherTo ShowTypeArgs
  }

showTypes :: PPOpt
showTypes = PPOpt (Do ShowTypes) (Do ShowGblStar) (Do ShowTypeArgs)

noTypes :: PPOpt
noTypes = showTypes { pp_types = Don't }

likeHaskell :: PPOpt
likeHaskell = PPOpt Don't Don't Don't

class AskOpt a where shouldI :: PPOpt -> WhetherTo a
instance AskOpt ShowGblStar  where shouldI = pp_gbl_star
instance AskOpt ShowTypes    where shouldI = pp_types
instance AskOpt ShowTypeArgs where shouldI = pp_type_args

ppTyped :: PPOpt -> Doc -> Doc -> Doc
ppTyped opt e t = case shouldI opt of
  Do ShowTypes -> parens (e <+> "::" $\ t)
  Don't -> e

ppProg :: PPOpt -> P a -> Program a -> Doc
ppProg t p (Program _ds fs) = vcat (map (ppFun t p) fs)

ppFun :: PPOpt -> P a -> Function a -> Doc
ppFun opt p (Function f ty e) =
    (p f <+> "::" $\ ppPolyType p ty) $$
    (p f <+> "=" $\ ppExpr 0 opt p e)

ppExpr :: Int -> PPOpt -> P a -> Expr a -> Doc
ppExpr i t p e0 = case e0 of
    Lcl x ty    -> ppId x ty
    Gbl x ty ts -> parensIf (not (null ts) && i > 1) $
        gstar <> ppPolyId x ty $\ ppTypeArgs t (sep [ "@" <+> ppType 1 p t' | t' <- ts ])
    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 t p) args
            pp_fun     = ppExpr 1 t p fun
        in  pp_fun $\ (sep pp_args)
    Lit x    -> integer x
    String s -> text (show s)
    Lam{} -> parensIf (i > 0) $
        let (args,body) = collectBinders e0
            pp_body     = ppExpr 0 t p body
            pp_args     = map (uncurry ppId) args
        in  "\\" <+> sep pp_args <+> "->" $\ pp_body
    Case e s alts -> parensIf (i > 0) $
        "case" <+> ppExpr 0 t p e <+> "of" <+> maybe empty (uncurry ppId) s $\
        inside "{ " "; " "}" (map (ppAlt t p) alts)
    Let fns e -> parensIf (i > 0) $
        ("let" <+> "{" $\ vcat (map (ppFun t p) fns) <+> "}" <+> "in") $$
        ppExpr 0 t p e
  where
    ppId     x ty = ppTyped t (p x) (ppType 0 p ty)
    ppPolyId x ty = ppTyped t (p x) (ppPolyType p ty)

    gstar = case shouldI t of
      Do ShowGblStar -> "*"
      Don't -> empty

ppTypeArgs :: PPOpt -> Doc -> Doc
ppTypeArgs opt d = case shouldI opt of
  Do ShowTypeArgs -> d
  Don't -> empty

ppAlt :: PPOpt -> P a -> Alt a -> Doc
ppAlt t p (pat,rhs) = ppPat t p pat <+> "->" $\ ppExpr 0 t p rhs

ppPat :: PPOpt -> P a -> Pattern a -> Doc
ppPat t p pat = case pat of
    Default           -> "_"
    ConPat c ty ts bs ->
        ppPolyId c ty $\
        sep [ ppTypeArgs t (sep [ "@" <+> ppType 1 p t' | t' <- ts ])
            , sep (map (uncurry ppId) bs)
            ]
    LitPat i          -> integer i
  where
    ppId     x ty = ppTyped t (p x) (ppType 0 p ty)
    ppPolyId x ty = ppTyped t (p x) (ppPolyType p ty)

ppPolyType :: P a -> PolyType a -> Doc
ppPolyType p (Forall [] ty) = ppType 0 p ty
ppPolyType p (Forall xs ty) = "forall" <+> sep (map p xs) <+> "." $\ ppType 0 p ty

ppType :: Int -> P a -> Type a -> Doc
ppType i p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> parensIf (i > 0) $ ppType 1 p t1 <+> "->" $\ ppType 0 p t2
    TyCon tc ts -> parensIf (i > 1) $ p tc $\ sep (map (ppType 1 p) ts)
    Integer     -> "Integer"

