{-# OPTIONS_GHC -fno-warn-deprecated-flags #-}
{-# LANGUAGE CPP,ScopedTypeVariables,PatternSignatures #-}
module Test.QuickSpec.CatchExceptions(catchExceptions) where

import Prelude hiding (catch)
import Control.Exception
import System.IO.Unsafe

#if __GLASGOW_HASKELL__ >= 610
type AnyException = SomeException
#else
type AnyException = Exception
#endif

catchExceptions :: Eq a => a -> Maybe a
catchExceptions x =
  unsafePerformIO $ do
    catch (evaluate (x == x) >> return (Just x))
          (\(_ :: AnyException) -> return Nothing)
