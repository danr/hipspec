module Test.QuickSpec(quickSpec,quickSpecDepth,module Test.QuickSpec.Term) where

import Test.QuickSpec.Term
import Test.QuickSpec.Equations

quickSpec :: r -> [Symbol] -> t -> Bool -> IO ()
quickSpec _ cons _ allow_eta_red = quickSpecDepth cons 3 allow_eta_red

quickSpecDepth :: [Symbol] -> Int -> Bool -> IO ()
quickSpecDepth cons depth allow_eta_red
    = laws allow_eta_red depth cons True (const True) (const True)
