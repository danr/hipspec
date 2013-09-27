module HipSpec.Property.Repr where

import HipSpec.Lang.Simple
import HipSpec.Lang.RichToSimple

import HipSpec.GHC.Utils

import HipSpec.Pretty

import Data.List (intercalate)

import Text.PrettyPrint

-- TODO: Print lists (x:[]) => [x], and tuples (,) x y => (x,y) properly
exprRepr' :: Int -> Expr String -> Doc
exprRepr' i e0 = case e0 of
    Var x _ -> text x
    App{}   ->
        let (fun,args) = collectArgs e0
            pp_args    = map (exprRepr' 2) args
            pp_args'   = map (exprRepr' 1) args
            pp_fun     = exprRepr' 0 fun
        in  case (oper (render pp_fun),pp_args') of
                (True,[])    -> parens pp_fun
                (True,[x])   -> parens (x <> pp_fun)
                (True,[x,y]) -> parensIf (i >= 1) $ x <> pp_fun <> y
                (True,x:y:_) -> parensIf (i >= 2) $ parens (x <> pp_fun <> y) <+> hsep (drop 2 pp_args)
                _            -> parensIf (i >= 2) $ pp_fun <+> hsep pp_args
    Lit x _ -> integer x

exprRepr :: Expr String -> String
exprRepr = render . exprRepr' 0

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf _    = id

oper :: String -> Bool
oper s = not (null s') && all (`elem` opSyms) s'
  where s' = filter (`notElem` ('_':['0'..'9'])) s

opSyms :: String
opSyms = ":!#$%&*+./<=>?@|^-~\\"

suggest :: Name' -> String
suggest nm = case nm of
    Old x          -> nameToString x
    New [LamLoc] _ -> "eta"
    New xs _       -> intercalate "_" (map suggest' xs)
    Bottom         -> "_|_"

suggest' :: Loc Name' -> String
suggest' CaseLoc     = "case"
suggest' LamLoc      = "lambda"
suggest' (LetLoc nm) = suggest nm

