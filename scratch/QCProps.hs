module Main where

import System.IO
import System.Environment
import Data.List
import Data.Char

main :: IO ()
main = do
  [f] <- getArgs
  c <- readFile f
  let out x = putStrLn $ "  quickCheck (printTestCase "
                         ++ show prop ++ " (" ++ prop ++ " " ++ inst ty ++ "))"
        where (prop,ty) = break (== ' ') x
              inst = unwords . map replace . words
              replace "" = ""
              replace s  = let (l,wr) = break isAlpha s
                               (w,r)  = span isAlpha wr
                               w' | null w || any isUpper w = w
                                  | otherwise               = "Int"
                           in l ++ w' ++ replace r
  mapM_ out $ filter ("::" `isInfixOf`)
            $ filter ((== "prop_") . take 5)
            $ lines c



