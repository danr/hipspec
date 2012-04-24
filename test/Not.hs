module Not where

import Prelude ()

data Bool = True | False

not True = False
not _    = True

not' True  = False
not' False = True