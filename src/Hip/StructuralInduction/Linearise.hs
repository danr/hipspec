{-

   Linearises the simple formulae and terms defined in Hip.StructuralInduction.

   This is only for testing, rather translate the formulae to your own
   representations.

-}
module Hip.StructuralInduction.Linearise where

import Hip.StructuralInduction

import Text.PrettyPrint hiding (Style)

data Style c v t = Style { linc :: c -> Doc
                         , linv :: v -> Doc
                         , lint :: t -> Doc
                         }

strStyle :: Style String String String
strStyle = Style { linc = text
                 , linv = text
                 , lint = text
                 }

linTerm :: Style c v t -> Term c v -> Doc
linTerm st tm = case tm of
    Var v    -> linv st v
    Con c [] -> linc st c
    Con c ts -> linc st c <> parens (csv (map (linTerm st) ts))
    Fun v ts -> linv st v <> parens (csv (map (linTerm st) ts))

linTypedVar :: Style c v t -> v -> t -> Doc
linTypedVar st v t = linv st v <+> colon <+> lint st t

linForm :: Style c v t -> (Doc -> Doc) -> Formula c v t -> Doc
linForm st par form = case form of
    Forall qs f -> par $ hang (bang <+> brackets (csv (map (uncurry (linTypedVar st)) qs)) <+> colon)
                              4
                              (linForm st parens f)
    xs :=> f -> par $ cat $ parList (punctuate (fluff ampersand)
                                               (map (linForm st parens) xs))
                          ++ [darrow <+> linForm st parens f]
    P xs -> char 'P' <> parens (csv (map (linTerm st) xs))

linFormula :: Style c v t -> Formula c v t -> String
linFormula st = render . linForm st id

csv :: [Doc] -> Doc
csv = hcat . punctuate comma

parList :: [Doc] -> [Doc]
parList []     = [parens empty]
parList [x]    = [x]
parList (x:xs) = (lparen <> x) : init xs ++ [last xs <> rparen]

ampersand :: Doc
ampersand = char '&'

pipe :: Doc
pipe = char '|'

bang :: Doc
bang = char '!'

fluff :: Doc -> Doc
fluff d = space <> d <> space

darrow :: Doc
darrow = text "=>"
