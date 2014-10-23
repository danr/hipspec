module Main where

import Prelude hiding ((++))
import Hip.HipSpec
import Hip.Prelude
import QuickSpec

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

rev :: [a] -> [a]
rev (x:xs) = rev xs ++ [x]
rev []     = []

qrev :: [a] -> [a] -> [a]
qrev (x:xs) ys = qrev xs (x:ys)
qrev []     ys = ys

prop_equal :: [a] -> Prop [a]
prop_equal xs = qrev xs [] =:= rev xs

main = hipSpec "QRev.hs" conf 3
  where
    conf = describe "QRev"
      [ var "x"     intType
      , var "y"     intType
      , var "z"     intType
      , var "xs"    listType
      , var "ys"    listType
      , var "zs"    listType
      , con "[]"    ([]   :: [Int])
      , con ":"     ((:)  :: Int  -> [Int] -> [Int])
      , con "++"    ((++) :: [Int] -> [Int] -> [Int])
      , con "rev"   (rev  :: [Int] -> [Int])
      , con "qrev"  (qrev :: [Int] -> [Int] -> [Int])
      ]
    intType   = intType  :: Int
    listType  = listType :: [Int]


















{-# ANN (++) "++" #-}
{-# ANN rev "rev" #-}
{-# ANN qrev "qrev" #-}
