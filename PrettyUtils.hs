{-# LANGUAGE OverloadedStrings #-}
module PrettyUtils where

import Text.PrettyPrint

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

