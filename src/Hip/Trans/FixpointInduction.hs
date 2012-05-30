{-# LANGUAGE RecordWildCards #-}
module Hip.Trans.FixpointInduction where

import Hip.Trans.ParserInternals
import Hip.Trans.Core
import Hip.Trans.Pretty
import Hip.Trans.NecessaryDefinitions
import Hip.Trans.Constructors
import Hip.Util

import Control.Arrow
import Control.Monad

import qualified Data.Set as S
import Data.Set (Set)

import Data.Generics.Uniplate.Data

import Data.Maybe
import Data.List

exampleCode :: [Decl]
exampleCode = parseDecls $ concatMap (++ ";")
  [ "even Z     = True"
  , "even (S x) = not (odd x)"
  , "odd Z      = True"
  , "odd (S x)  = not (even x)"
  ]

exampleCode2 = parseDecls $ unlines
 [ "qs0 f q0 xs = scanr f q0 xs ;"
 , "cs2 u1 u2 u3 u4 = case T4 u1 u2 u3 u4 of {"
 , "                           T4 f q0 xs (Cons q3 w) -> q3"
 , "                       } ;"
 , "q1 f q0 xs = cs2 f q0 xs (qs0 f q0 xs) ;"
 , "scanr u1 u2 u3 = case T3 u1 u2 u3 of {"
 , "                      T3 f q0 Nil -> Cons q0 Nil;"
 , "                      T3 f q0 (Cons x xs) -> Cons (f x (q1 f q0 xs)) (qs0 f q0 xs)"
 , "                  } ;"
 ]

unRec = "oi"

fixMe = "*I"

-- Lifts the functions up for suitable fixpoint induction Assumes all
-- decls are fundecls, and that the functions are recursive.
--
-- Algorithm for lifting fs of definitions ds:
--     Find all functions rs that use those in fs. The functions fs
--     are necessarily members there.
--     For all functions in rs, make new decls where the function f
--     is defined as f.fixMe, and all calls to f are now called f.unRec
fixate :: [Name] -> [Decl] -> [Decl]
fixate fs ds = mapMaybe mod ds
  where
    fset    :: Set Name
    fset    = S.fromList fs

    rs      :: Set Name
    rs      = callers ds fset

    fsUnRec :: [(Name,Name)]
    fsUnRec = map (id &&& (++ unRec)) fs

    fsFixMe :: [(Name,Name)]
    fsFixMe = map (id &&& (++ fixMe)) fs

    restNames :: [(Name,Name)]
    restNames = map (id &&& (++ ".copy")) (S.toList (rs S.\\ fset))

    bodyList :: [(Name,Name)]
    bodyList = fsUnRec ++ restNames

    nameList :: [(Name,Name)]
    nameList = fsFixMe ++ restNames

    mod :: Decl -> Maybe Decl
    mod (Func name args body) = do
        guard (not $ S.null $ rs `S.intersection` (S.insert name (usedFs body)))
        return $ Func (fromMaybe (error $ "fixate: " ++ name ++ "lost")
                                 (lookup name nameList))
                      args
                      (substVarsBody bodyList body)
    mod _ = Nothing

type ExprTup = (Expr,Expr)

data FixProof = FixProof { baseDecls :: [Decl]
                         , stepDecls :: [Decl]
                         , base :: ExprTup
                         , anyt :: ExprTup
                         , hyp  :: ExprTup
                         , step :: ExprTup
                         , fixedFuns :: [Name]
                         }

instance Show FixProof where
  show (FixProof {..}) = unlines $
     [ "baseDecls: "
     , unlines (map show baseDecls)
     , "stepDecls: "
     , unlines (map show stepDecls)
     , "base: " ++ showTup base
     , "anyt: " ++ showTup anyt
     , "hyp:  " ++ showTup hyp
     , "step: " ++ showTup step
     , "fixed functions: " ++ unwords fixedFuns
     ]
     where showTup (l,r) = show l ++ " = " ++ show r

(+-+) :: [a] -> [a] -> [a]
(x:xs) +-+ ys = x:(ys +-+ xs)
[]     +-+ ys = ys

powSubst :: [(Name,Name)] -> Expr -> [Expr]
powSubst m = transformM f
  where f e@(Var x)    = [e] +-+ [Var x'    | Just x' <- [lookup x m]]
        f e@(App x as) = [e] +-+ [App x' as | Just x' <- [lookup x m]]
        f e = [e]

testPowSubst = mapM_ print
             $ powSubst [("x","X"),("g","G")]
                        (parseExpr "eq (x x) (x x)")

proofByFixpoint :: [Decl] -> Set Name -> Expr -> Expr -> [FixProof]
proofByFixpoint ds recset lhs rhs =
     zipWith5 mkFixProof (candidates (bottomFunName . arityLookup))
                         (candidates (++ anySuf))
                         (candidates (++ unRec))
                         (candidates (++ fixMe))
                         [0..]
  where
    funcset :: Set Name
    funcset = eqNameSet lhs rhs `S.intersection` recset

    functions :: [Name]
    functions = S.toList $ funcset

    eqNameSet :: Expr -> Expr -> Set Name
    eqNameSet l r = (usedFs l `S.union` usedFs r)

    candidates :: (Name -> Name) -> [(Expr,Expr)]
    candidates f = drop 1 [ (l,r) | l <- cand lhs, r <- cand rhs ]
      where cand = powSubst (map (id &&& f) functions)

    mkFixProof :: ExprTup -> ExprTup -> ExprTup -> ExprTup -> Int -> FixProof
    mkFixProof base anyt hyp step@(l,r) x = FixProof
        { baseDecls = [ bottomFun n | n <- nub (map arityLookup fixedFuns) ]
        , stepDecls = fixate fixedFuns ds
        , base = base
        , anyt = anyt
        , hyp  = hyp
        , step = step
        , fixedFuns = show x : fixedFuns
        }
      where
        fixedFuns = map (reverse . drop (length fixMe) . reverse)
                  . filter (fixMe `isSuffixOf`)
                  . S.toList
                  $ eqNameSet l r

    bottomFunName n = "const.bottom" ++ show n
    bottomFun n     = Func (bottomFunName n)
                           (vars n)
                           (Expr (Var bottomName))

    vars n = take n ([1..] >>= flip replicateM ['a'..'z'])

    arityLookup f =
         fromMaybe (error $ "proofByFixpoint induction " ++
                            "on non-existent function" ++ f)
       $ lookup f
       $ map (declName &&& length . declArgs) ds

testFPI = mapM_ print $ map step $ proofByFixpoint (parseDecls "f = f;") (S.fromList ["f"]) (parseExpr "f (f x)") (parseExpr "f (f x)")