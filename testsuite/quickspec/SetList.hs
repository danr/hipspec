{-# LANGUAGE DeriveDataTypeable, TypeFamilies, Rank2Types #-}
module Main where

import Data.Typeable
import Data.Function
import qualified Data.List as L

import Test.QuickCheck
import Test.QuickSpec

import Control.Applicative hiding (empty)

-- Monomorphised to Int elements
-- Invariant : no duplicates
newtype SetList = SetList { elements :: [Int] }
  deriving (Show,Typeable)

-- Equality and Ordering is sorted equality           
instance Eq SetList where           
  SetList xs == SetList ys = L.sort xs == L.sort ys
  
instance Ord SetList where
  SetList xs `compare` SetList ys = L.sort xs `compare` L.sort ys

-- Only works if the binary operaton does not introduce duplicates
mkBinOp :: (forall a . Eq a => [a] -> [a] -> [a]) 
        -> SetList -> SetList -> SetList
mkBinOp (@@) (SetList xs) (SetList ys) = SetList (xs @@ ys)

(/\) :: SetList -> SetList -> SetList
(/\) = mkBinOp L.intersect

(\/) :: SetList -> SetList -> SetList
(\/) = mkBinOp L.union

(\\) :: SetList -> SetList -> SetList
(\\) = mkBinOp (L.\\)

singleton :: Int -> SetList
singleton x = SetList [x]

empty :: SetList
empty = SetList []

instance Arbitrary SetList where
  arbitrary = sized $ \s -> do
    l <- choose (0,s)
    xs <- map (\(Positive x) -> x) <$> vector l
    return (SetList (scanl (+) 0 xs))
    
instance Classify SetList where
  type Value SetList = SetList
  evaluate = return

-- One interesting thing is that no laws with singleton shows up  
spec_module = describe "SetLists"
              [ var "a" elemType
              , var "b" elemType
              , var "A" setType
              , var "B" setType
              , var "C" setType
              , con "singleton" singleton
              , con "empty" empty
              , con "/\\" (/\)
              , con "\\/" (\/)
              , con "\\\\" (\\)
              ]                
  where setType  = undefined :: SetList
        elemType = undefined :: Int

run_spec = quickSpec spec_module True

main = run_spec

prop_absorb_intersect :: SetList -> SetList -> Bool
prop_absorb_intersect a b = a \/ (a /\ b) == a

prop_absorb_union :: SetList -> SetList -> Bool
prop_absorb_union a b = a /\ (a \/ b) == a

prop_comm_intersect :: SetList -> SetList -> Bool
prop_comm_intersect a b = a /\ b == b /\ a 

prop_comm_union :: SetList -> SetList -> Bool
prop_comm_union a b = a \/ b == b \/ a 
