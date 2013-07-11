{-# LANGUAGE OverloadedStrings #-}
module PrettyUtils where

import Text.PrettyPrint

-- | Pretty printing kit, first is for variable bindings, second is for variables
--   (to be able to say where to print types and where to ignore it)
type Kit a = (a -> Doc,a -> Doc)

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

csv :: [Doc] -> Doc
csv = inside "(" "," ")"

inside :: Doc -> Doc -> Doc -> [Doc] -> Doc
inside l _ r [] = l <> r
inside l p r (x:xs) = cat (go (l <> x) xs)
  where
    go y []     = [y,r]
    go y (z:zs) = y : go (p <> z) zs

