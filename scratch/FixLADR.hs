module Main where

main = interact (unlines . map adjust . lines)

adjust s | '#' `elem` s = takeWhile (/= '#') s ++ "."
         | otherwise    = s

