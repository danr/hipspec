
module Lang.CoreLint where

import Bag
import CoreLint
import CoreSyn

import HipSpec.GHC.Utils

import System.IO

coreLint :: [CoreBind] -> IO ()
coreLint bs = do
    let (msgs1,msgs2) = lintCoreBindings bs
    mapM_ (mapBagM_ (hPutStrLn stderr . portableShowSDoc)) [msgs1,msgs2]

