module Sorting where

import Prelude(Bool(..),undefined)
import HipSpec
import Definitions
import Properties(prop_T14)
import Test.QuickSpec.Signature

-- -- Nick Style:
-- def :: NList -> NList -> NList
-- def xs ys = if sorted xs then ys else NNil
--
-- prop_def x = def x (NCons Z NNil) =:= NCons Z NNil ==> proveBool (sorted x)

-- Koen Style:
whenSorted :: NList -> NList
whenSorted xs = if sorted xs then xs else NNil

-- Use this, or the signature with depth 4 below (takes a lot of time)
prop_koen x xs = sorted (insert x (whenSorted xs)) =:= True

sig = signature
    [Test.QuickSpec.Signature.fun0 "False" (False)
	,Test.QuickSpec.Signature.fun0 "True" (True)
	,Test.QuickSpec.Signature.fun0 "NNil" (Definitions.NNil)
	,Test.QuickSpec.Signature.fun2 "NCons" (Definitions.NCons)
	,Test.QuickSpec.Signature.fun0 "Z" (Definitions.Z)
	,Test.QuickSpec.Signature.fun1 "S" (Definitions.S)
	,Test.QuickSpec.Signature.fun1 "sorted" (Definitions.sorted)
	,Test.QuickSpec.Signature.fun1 "isort" (Definitions.isort)
	,Test.QuickSpec.Signature.fun2 "insert" (Definitions.insert)
	,Test.QuickSpec.Signature.fun2 "<=" (Definitions.<=)
	,Test.QuickSpec.Signature.fun1 "whenSorted" (Sorting.whenSorted)
	,vars ["x","y","z"] (Prelude.undefined :: Bool)
	,vars ["x","y","z"] (Prelude.undefined :: Definitions.NList)
	,vars ["x","y","z"] (Prelude.undefined :: Definitions.Nat)
	,Test.QuickSpec.Signature.withTests 100
	,Test.QuickSpec.Signature.withQuickCheckSize 20
	,Test.QuickSpec.Signature.withSize 1000
    ,Test.QuickSpec.Signature.withDepth 4
    ]


