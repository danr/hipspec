{-# LANGUAGE OverloadedStrings #-}
module HipSpec.Lang.PrettyUtils where

import Text.PrettyPrint

infixr 1 $\

($\) :: Doc -> Doc -> Doc
d1 $\ d2 = hang d1 2 d2

data Types = Show | Don'tShow

ppTyped :: Types -> Doc -> Doc -> Doc
ppTyped Show e t = parens (e <+> "::" $\ t)
ppTyped _    e _ = e

-- | Pretty printing kit.
data P a = PK
    { p :: a -> Doc
    , pp_infix :: a -> Bool
    }

-- | Pretty printing kit for polymorphic FOL
--   Here, we want to differentiate between symbols and variables in tff
data PP a b = PP
    { pp_symb  :: a -> Doc
    , pp_var   :: b -> Doc
    }

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

csv :: [Doc] -> Doc
csv = inside "(" "," ")"

starsep :: [Doc] -> Doc
starsep = inside "(" "*" ")"

inside :: Doc -> Doc -> Doc -> [Doc] -> Doc
inside _ _ _ []     = empty
inside l p r (x:xs) = cat (go (l <> x) xs)
  where
    go y []     = [y,r]
    go y (z:zs) = y : go (p <> z) zs

sepWith :: Doc -> [Doc] -> Doc
sepWith _ []     = empty
sepWith p (x:xs) = sep (go x xs)
  where
    go y []     = [y]
    go y (z:zs) = y : go (p <+> z) zs

