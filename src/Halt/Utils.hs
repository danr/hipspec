module Halt.Utils where

import Id
import Name
import Outputable
import PprCore
import CoreSyn

import FOL.Syn

import Data.Char

-- | Short representation of an Id/Var to String (unsafely for now)
idToStr :: Id -> String
idToStr = showSDocOneLine . ppr . maybeLocaliseName . idName
  where
    maybeLocaliseName n | isSystemName n = n
                        | otherwise      = localiseName n

-- | Shows a Core Expression
showExpr :: CoreExpr -> String
showExpr = showSDoc . pprCoreExpr

-- | The arity of an expression if it is a lambda
exprArity :: CoreExpr -> Int
exprArity e = length as
  where (_,as,_) = collectTyAndValBinders e


-- | Removes the type arguments
trimTyArgs :: [CoreArg] -> [CoreArg]
trimTyArgs = filter (not . isTyArg)
  where
    isTyArg Type{} = True
    isTyArg _      = False

minPred :: Term -> Formula
minPred tm = Rel (RelName "min") [tm]

mkFun :: Var -> [Term] -> Term
mkFun = Fun . FunName . map toLower . idToStr

implies :: Bool -> [Formula] -> Formula -> Formula
implies cnf fs f | cnf       = fs ~\/ f
                 | otherwise = fs =:=> f
 where
   [] =:=> phi = phi
   xs =:=> phi = foldl1 (/\) xs ==> phi

   xs ~\/ phi = foldr (\/) phi (map neg xs)

foldFunApps :: Term -> [Term] -> Term
foldFunApps = foldl (\x y -> Fun (FunName "app") [x,y])

mkPtr :: Var -> Term
mkPtr = (`Fun` []) . FunName . (++ "ptr") . map toLower . idToStr

mkVarName :: Var -> VarName
mkVarName = VarName . capInit . idToStr
  where
    capInit (x:xs) | isAlpha x = toUpper x : xs
                   | otherwise = 'Q':x:xs
                        -- ^ needs escaping here
                        --   example: (>) as an argument to a sortBy function
    capInit "" = "Q"

mkVar :: Var -> Term
mkVar = FVar . mkVarName



