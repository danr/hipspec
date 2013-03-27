module HipSpec.Lint (lint) where

import Bag
import CoreLint
import CoreSyn

import Halo.Shared

import HipSpec.Monad

lint :: String -> [CoreBind] -> HS ()
lint s bs = liftIO $ do
    putStrLn $ "== " ++ s ++ " CORE LINT =="
    let (msgs1,msgs2) = lintCoreBindings bs
    mapM_ (mapBagM_ (putStrLn . portableShowSDoc)) [msgs1,msgs2]


