{-# LANGUAGE ScopedTypeVariables, ParallelListComp, PatternGuards,
             ExistentialQuantification, FlexibleContexts #-}
module Halt.FOL.Rename where

import Var
import Name
import Id
import Outputable

import Halt.Util

import Halt.FOL.Internals.Internals
import Halt.FOL.Operations
import Halt.FOL.Abstract

import Data.Bimap (Bimap)
import qualified Data.Bimap as B
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.Data
import Data.Char
import Data.Maybe

renameClauses :: [Clause'] -> [StrClause]
renameClauses clauses =
    let renameFuns :: Clause q Var -> Clause q String
        renameFuns = mkFunRenamer (map WrapClause clauses)

        clauses' = map (renameQVar suggest) (map renameFuns clauses)
          where
            suggest :: Var -> [String]
            suggest v = [ case s of
                            x:xs | isAlpha x -> toUpper x:xs
                                 | otherwise -> 'Q':s
                            []   -> 'Q':show i
                        | s <- varSuggest v
                        | i <- [(0 :: Int)..]
                        ]

     in  clauses'

data WrappedClause'
  = forall q . (Data q,Data (Clause q Var)) => WrapClause (Clause q Var)

mkFunRenamer :: [WrappedClause'] -> Clause q Var -> Clause q String
mkFunRenamer clauses =
    let symbols :: [Var]
        symbols = nubSorted $ concatMap (\(WrapClause cl) -> allSymbols cl) clauses

        rep_map :: Map Var String
        rep_map = B.toMap (foldr (allot varSuggest protectedWiredIn)
                                 B.empty symbols)

        replace :: Var -> String
        replace v = case M.lookup v rep_map of
                        Just s  -> s
                        Nothing -> error $ "renameFuns: " ++ showSDoc (ppr v)
                                        ++ " not renamed!"

    in  clauseMapTerms (replaceVarsTm replace) id

renameQVar :: forall q . (Data q,Ord q)
            => (q -> [String])
            -> Clause q String -> Clause String String
renameQVar suggest cl =
    let symbols :: Set String
        symbols = S.fromList (allSymbols cl)

        quants :: [q]
        quants = allQuant cl

        rep_map :: Map q String
        rep_map = B.toMap (foldr (allot suggest (symbols `S.union` protectedWiredIn))
                                 B.empty quants)

        replace :: q -> String
        replace q = case M.lookup q rep_map of
                        Just s  -> s
                        Nothing -> error $ "renameQVar: quantified variable not renamed!"

    in  clauseMapTerms (replaceQVarsTm replace) replace cl

allot :: Ord v => (v -> [String]) -> Set String -> v
               -> Bimap v String -> Bimap v String
allot suggest protected var bimap = B.insert var selected bimap
  where
    selected :: String
    selected = head [ cand
                    | cand <- suggest var
                    , cand `B.notMemberR` bimap
                    , cand `S.notMember` protected
                    ]

varSuggest :: Var -> [String]
varSuggest var = candidates
  where
    name :: Name
    name = idName var

    strs :: [String]
    strs = map (toTPTPid . showSDoc)
               [ppr (nameOccName name),ppr name]

    candidates :: [String]
    candidates = strs ++ [ s ++ "_" ++ show x | s <- strs , x <- [(0 :: Int)..]]


toTPTPid :: String -> String
toTPTPid s | Just x <- M.lookup s prelude = x
           | otherwise                    = escape (lower s)

escape :: String -> String
escape = concatMap (\c -> fromMaybe [c] (M.lookup c escapes))

lower :: String -> String
lower = map toLower

protectedWiredIn :: Set String
protectedWiredIn = S.fromList ["app","min","cf","bad","unr"]

escapes :: Map Char String
escapes = M.fromList
    [ ('\'',"prime")
    , ('!' ,"bang")
    , ('#' ,"hash")
    , ('$' ,"dollar")
    , ('%' ,"pc")
    , ('*' ,"star")
    , ('+' ,"plus")
    , ('.' ,"_")
    , ('/' ,"slash")
    , ('<' ,"less")
    , ('=' ,"equals")
    , ('>' ,"greater")
    , ('?' ,"qmark")
    , ('\\',"bslash")
    , ('^' ,"hat")
    , ('|' ,"pipe")
    , (':' ,"colon")
    , ('-' ,"minus")
    , ('~' ,"tilde")
    , ('@' ,"at")

    , ('{' ,"rb")
    , ('}' ,"lb")
    , ('[' ,"rbr")
    , (']' ,"lbr")
    , ('(' ,"rp")
    , (')' ,"lp")
    , (',' ,"comma")
    ]

prelude :: Map String String
prelude = M.fromList
   [ ("[]","nil")
   , (":","cons")
   , ("()","unit")
   , ("(,)","tup")
   , ("(,,)","triple")
   , ("(,,,)","quad")
   , ("(,,,,)","quint")

   , ("++","append")
   , ("!!","index")

   , ("+","add")
   , ("-","sub")
   , ("/","div")
   , ("*","mul")
   , ("^","pow")
   , ("**","fpow")
   , ("^^","ipow")

   , (".","comp")
   , ("$","apply")

   , ("&&","and")
   , ("||","or")

   , ("==","eq")
   , ("/=","ne")

   , (">","gt")
   , ("<","lt")
   , (">=","ge")
   , ("<=","le")

   , (">>=","bind")
   , ("=<<","mapply")
   , (">>","then")
   , ("<<","after")

   , ("<$>","fmap")
   , ("<*>","ap")
   ]

