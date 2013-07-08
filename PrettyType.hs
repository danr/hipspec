{-# LANGUAGE OverloadedStrings #-}
module PrettyType where

import Text.PrettyPrint

import PrettyUtils
import Type

ppType :: Int -> (a -> Doc) -> Type a -> Doc
ppType i p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> parensIf (i > 0) $ ppType 1 p t1 <+> "->" <+> ppType 0 p t2
    TyCon tc ts -> p tc <+> sep (map (ppType 1 p) ts)
    Star        -> "*"
    Forall{}    -> parensIf (i > 0) $
        let (tvs,t) = collectForalls t0
        in  hang ("forall" <+> sep (map p tvs) <+> ".") 2 (ppType 0 p t)

