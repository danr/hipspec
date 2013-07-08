{-# LANGUAGE PackageImports #-}
module CoreLint where

import Bag
import "ghc" CoreLint
import CoreSyn

import Utils

coreLint :: [CoreBind] -> IO ()
coreLint bs = do
    let (msgs1,msgs2) = lintCoreBindings bs
    mapM_ (mapBagM_ (putStrLn . portableShowSDoc)) [msgs1,msgs2]

