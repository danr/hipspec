module Hip.StructuralInduction.Test where

import Hip.StructuralInduction
import Hip.StructuralInduction.Linearise

-- | A small test envirenment of Ordinals, Naturals, Integers,
--   Lists, Trees and Expressions.
testEnv :: TyEnv String String
testEnv "Ord" = Just [("zero",[])
                     ,("succ",[Rec "Nat"])
                     ,("lim",[Exp "Nat -> Ord" ["Nat"]])
                     ]
testEnv "Nat" = Just [("zero",[])
                     ,("succ",[Rec "Nat"])
                     ]
testEnv "Int" = Just [("pos",[NonRec "Nat"])
                     ,("neg",[NonRec "Nat"])
                     ]
testEnv list@('L':'i':'s':'t':' ':a) =
    Just [("nil",[])
         ,("cons",[NonRec a,Rec list])
         ]
testEnv tree@('T':'r':'e':'e':' ':a) =
    Just [("leaf",[NonRec a])
         ,("fork",[Rec tree,Rec tree])
         ]
testEnv tree@('T':'r':'e':'e':'\'':' ':a) =
    Just [("empty",[])
         ,("branch",[Rec tree,NonRec a,Rec tree])
         ]
testEnv expr@('E':'x':'p':'r':' ':v) =
    Just [("var",[NonRec v])
         ,("lit",[NonRec "Int"])
         ,("add",[Rec expr,Rec expr])
         ,("mul",[Rec expr,Rec expr])
         ,("neg",[Rec expr,Rec expr])
         ]
testEnv xs = Nothing

-- | Specify the type of every variable, then on which coordinates of
--   P to do induction on. This function then takes care of the
--   plumbing and prints the results.
testStrInd :: [(String,String)] -> [Int] -> IO ()
testStrInd vars coords = putStr $ unlines
                                $ map ( (++ ".")
                                      . linFormula strStyle
                                      . unV (\x i -> x ++ show i))
                                $ structuralInduction testEnv vars coords

-- Various tests --------------------------------------------------------------

intInd      = testStrInd [("X","Int")]

intInd2     = testStrInd [("X","Int"),("Y","Int")]

intInd3     = testStrInd [("X","Int"),("Y","Int"),("Z","Int")]

natInd      = testStrInd [("X","Nat")]

natInd2     = testStrInd [("X","Nat"),("Y","Nat")]

natInd3     = testStrInd [("X","Nat"),("Y","Nat"),("Z","Nat")]

listInd     = testStrInd [("Xs","List a")]

natListInd  = testStrInd [("Xs","List Nat")]

ordListInd  = testStrInd [("Xs","List Ord")]

ordInd      = testStrInd [("X","Ord")]

treeInd     = testStrInd [("T","Tree a")]

exprInd     = testStrInd [("E","Expr a")]

tree'Ind    = testStrInd [("T","Tree' a")]

treeTreeInd = testStrInd [("T","Tree Tree a")]

