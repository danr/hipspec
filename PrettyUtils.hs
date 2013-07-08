module PrettyUtils where

import Text.PrettyPrint

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

