{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Hip.Trans.Pretty (prettyCore) where

import Hip.Trans.Core
import Text.PrettyPrint.HughesPJ
import Hip.Trans.Constructors

prettyCore :: P a => a -> String
prettyCore = render . p

enclose :: Bool -> Doc -> Doc
enclose True  = parens
enclose False = id

class P a where
  p :: a -> Doc

instance P Decl where
  p (Func n as b) = text n <+> hsep (map text as) <+> equals <+> p b <+> semi
  p (Data n as cs) = text "data" <+> text n <+> hsep (map text as) <+> equals
                                 <+> hsep (punctuate (text " |") (map p cs)) <+> semi
  p (TyDecl n ty) = text n <+> text "::" <+> p ty <+> semi

instance P Cons where
  p (Cons n as) = text n <+> hsep (map (pty 1) as)

instance P Type where
  p = pty 2

pty :: Int -> Type -> Doc
pty _ (TyVar n) = text n
pty l (TyApp ts) = enclose (l <= 1) $ hsep (punctuate (text " ->") (map (pty 1) ts))
pty l (TyCon n ts) = enclose (l <= 1 && not (null ts))
                   $ text n <+> hsep (map (pty 1) ts)

instance P Body where
  p (Case e brs) = text "case" <+> p e <+> text "of" <+> lbrace
                   $$ nest 4 (vcat (punctuate semi (map p brs)))
                   $$ rbrace
  p (Expr e)     = p e

instance P Expr where
  p = pexpr 2

pexpr :: Int -> Expr -> Doc
pexpr l (App n es)   = enclose (l <= 1) $ text n <+> hsep (map (pexpr 1) es)
pexpr l (Con n es)   = enclose (l <= 1) $ text n <+> hsep (map (pexpr 1) es)
pexpr l (e ::: t)    = enclose (l <= 1) (pexpr 1 e <+> text "::" <+> p t)
pexpr _ (Var n)      = text n
pexpr _ (IsBottom e) = pexpr 2 e <+> text "==" <+> text bottomName

instance P Branch where
  p (pat :-> e) = p pat <+> text "->" <+> p e

instance P PMG where
  p (Guard pat e) = p pat <+> text "|" <+> p e
  p (NoGuard pat) = p pat

instance P Pattern where
  p = ppat 2

ppat :: Int -> Pattern -> Doc
ppat _ (PVar n)    = text n
ppat _ (PCon n []) = text n
ppat l (PCon n ps) = enclose (l <= 1) (text n <+> hsep (map (ppat 1) ps))

instance P Name where
  p = text

-- Orphan instances
instance Show Decl where show = prettyCore
instance Show Body where show = prettyCore
instance Show Expr where show = prettyCore
instance Show Branch where show = prettyCore
instance Show PMG where show = prettyCore
instance Show Pattern where show = prettyCore
instance Show Type where show = prettyCore
