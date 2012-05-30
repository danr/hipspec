module Hip.Trans.Constructors where

import Hip.Trans.Core

-- | The name for bottom
bottomName :: Name
bottomName = "_|_"

-- | The bottom pattern
bottomP :: Pattern
bottomP = pcon0 bottomName

-- | The bottom expression
bottom :: Expr
bottom = con0 bottomName

-- | True
trueName :: Name
trueName = "True"

-- | The true pattern
trueP :: Pattern
trueP = pcon0 trueName

-- | False
falseName :: Name
falseName = "False"

anySuf :: Name
anySuf = ".any"
