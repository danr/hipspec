module Test.QuickSpec(quickSpec,quickSpecDepth,module Test.QuickSpec.Term) where

import Test.QuickSpec.Term
import Test.QuickSpec.Equations

quickSpec :: [Symbol] -> t -> IO ()
quickSpec cons cond = laws 3 cons cond (const True) (const True)

quickSpecDepth :: [Symbol] -> Int -> IO ()
quickSpecDepth cons depth = laws depth cons True (const True) (const True)

