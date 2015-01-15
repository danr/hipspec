{-# LANGUAGE OverloadedStrings, RecordWildCards, ViewPatterns #-}
-- | Pretty-printing the rich language, parameterised on whether to print
--   types of variables.
module HipSpec.Lang.PrettyTIF where

import Text.PrettyPrint

import HipSpec.Lang.Rich
import HipSpec.Lang.PrettyUtils hiding (pp_symb,pp_var)
import HipSpec.Lang.Type

-- TIF pretty priting Kit
data TK a = TK
  { pp_symb :: a -> Doc
  , pp_var  :: a -> Doc
  }

tif :: Doc -> Doc -> Doc -> Doc
tif name typ cntnt = ("tif" <> "(" <> name <> "," <+> typ <> ",") $\ (cntnt <> ").")

ppProg :: TK a -> Program a -> Doc
ppProg tk (Program ds fs) = vcat (concatMap (ppData tk) ds ++ concatMap (ppFun tk) fs)

ppData :: TK a -> Datatype a -> [Doc]
ppData tk (Datatype tc tvs cons) =
       [ tif (pp_symb tc) "type"
           (pp_symb tc `typeSig` ppKind (length tvs))
       ]
    ++ map (ppCon tk tc tvs) cons
    ++ [""]
  where TK{..} = tk

typeSig :: Doc -> Doc -> Doc
x `typeSig` t = x <+> ":" $\ t

ppCon :: TK a -> a -> [a] -> Constructor a -> Doc
ppCon tk tc tvs (Constructor c as) =
    tif
      (pp_symb c)
      "constructor"
      (typeSig
         (pp_symb c)
         (ppPolyType tk (Forall tvs (makeArrows as (TyCon tc (map TyVar tvs))))))
  where TK{..} = tk

ppKind :: Int -> Doc
ppKind 0 = tType
ppKind n = tuple (replicate n tType) <+> ">" $\ tType

tuple :: [Doc] -> Doc
tuple = sep . punctuate " *"

tType :: Doc
tType = "$tType"

ppTyQuant :: TK a -> Doc -> [(a,Type a)] -> Doc -> Doc
ppTyQuant tk q xs d = ppQuant tk q [ (x,ppType tk t) | (x,t) <- xs ] d

ppQuant :: TK a -> Doc -> [(a,Doc)] -> Doc -> Doc
ppQuant tk q xs d = case xs of
    [] -> d
    _  -> (q <> bsv [ pp_var x `typeSig` t | (x,t) <- xs] <> ":") $\ d
  where
    bsv [] = empty
    bsv xs = brackets (fsep (punctuate "," xs))
    TK{..} = tk

ppFun :: TK a -> Function a -> [Doc]
ppFun tk (Function f ty@(Forall tvs _) (collectBinders -> (xs,e))) =
  [ tif
      (pp_symb f)
      "type"
      (pp_symb f `typeSig` ppPolyType tk ty)
  , tif
      (pp_symb f)
      "definition"
      -- (ppQuant tk "!" ([ (tv,tType) | tv <- tvs ] ++ [ (x,ppType tk t) | (x,t) <- xs ])
        (ppExpr tk (Gbl f ty (map TyVar tvs) `apply` map (uncurry Lcl) xs) <+> "=" $\
         ppExpr tk e)
      -- )
   , ""
   ]
  where TK{..} = tk

-- Assumes all functions calls are perfectly saturated, for now
ppExpr :: TK a -> Expr a -> Doc
ppExpr tk e0 = case collectArgs e0 of
    (Lcl x _ty,[])    -> pp_var x
    (Gbl x _ty ts,[]) -> pp_symb x
    (Gbl x _ty ts,as) ->
      pp_symb x <> "(" $$\
        fsep (punctuate "," (map (ppType tk) ts ++ map (ppExpr tk) as)) <> ")"
    (Lit x,[])        -> integer x
    (String s,[])     -> text (show s)
    (Case e Nothing alts,[]) ->
        ("case" <> "(" <> ppExpr tk e <> ",") $\
          (sep (punctuate "," (map (ppAlt tk) alts)) <> ")")
    (Lam{},_) -> "lambda"
    (Let{},_) -> "let"
    (_,_:_)   -> "over-saturated"
  where TK{..} = tk

csv' :: [Doc] -> Doc
csv' [] = empty
csv' xs = parens (sep (punctuate "," xs))

csv'' :: [Doc] -> Doc
csv'' [] = empty
csv'' xs = sep (punctuate "," xs)

ppAlt :: TK a -> Alt a -> Doc
ppAlt tk (pat,rhs) = ppPat tk pat <+> "=>" $\ ppExpr tk rhs

ppPat :: TK a -> Pattern a -> Doc
ppPat tk pat = case pat of
    Default            -> "_"
    ConPat c _ty ts bs ->
        pp_symb c <> csv'
           (map (ppType tk) ts ++ [ pp_var x {- `typeSig` ppType tk t -} | (x,t) <- bs ])
    LitPat i           -> integer i
  where TK{..} = tk

ppPolyType :: TK a -> PolyType a -> Doc
ppPolyType tk (Forall xs ty) = ppQuant tk "!>" [ (x,tType) | x <- xs ] (ppTopType tk ty)

-- collect arrows arguments , and print them as a tuple with *
ppTopType :: TK a -> Type a -> Doc
ppTopType tk t = case collectArrTy t of
    ([],r) -> ppType tk r
    (as,r) -> tuple (map (ppType tk) as) <+> ">" $\ ppType tk r

ppType :: TK a -> Type a -> Doc
ppType tk t0 = case t0 of
    TyVar x     -> pp_var x
    ArrTy t1 t2 -> parens (ppType tk t1 <+> "=>" $\ ppType tk t2)
    TyCon tc ts -> pp_symb tc <> csv' (map (ppType tk) ts)
    Integer     -> "$int"
  where TK{..} = tk
