{-# LANGUAGE ScopedTypeVariables, ParallelListComp, PatternGuards,
             ExistentialQuantification, FlexibleContexts #-}
module Halo.FOL.Rename where

import Var
import Name
import Id
import Outputable

import Halo.Util

import Halo.FOL.Internals.Internals
import Halo.FOL.Operations
import Halo.FOL.Abstract

import Data.Bimap (Bimap)
import qualified Data.Bimap as B
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.Char
import Data.Maybe

renameClauses :: [Clause'] -> ([StrClause],Map String Var)
renameClauses clauses =
    let rename_funs :: Clause' -> Clause Var String
        str_map :: Map String Var
        (rename_funs,str_map) = mkFunRenamer clauses

        clauses' = map (renameQVar suggest) (map rename_funs clauses)
          where
            suggest :: Var -> [String]
            suggest v = [ case escape qvarEscapes s of
                            x:xs | isAlpha x -> toUpper x:xs
                            _ -> 'Q':show i
                        | s <- varSuggest v
                        | i <- [(0 :: Int)..]
                        ]

     in  (clauses',str_map)

mkFunRenamer :: [Clause'] -> (Clause' -> Clause Var String,Map String Var)
mkFunRenamer clauses =
    let symbols :: [Var]
        symbols = nubSorted $ concatMap allSymbols' clauses

        rep_bimap :: Bimap Var String
        rep_bimap = foldr (allot varSuggest protectedWiredIn) B.empty symbols

        rep_map :: Map Var String
        rep_map = B.toMap rep_bimap

        str_map :: Map String Var
        str_map = B.toMapR rep_bimap

        replace :: Var -> String
        replace v = case M.lookup v rep_map of
                        Just s  -> s
                        Nothing -> error $ "renameFuns: " ++ showSDoc (ppr v)
                                        ++ " not renamed!"

    in  (clauseMapTerms (replaceVarsTm replace) id,str_map)

renameQVar :: forall q . Ord q => (q -> [String]) -> Clause q String -> Clause String String
renameQVar suggest cl =
    let symbols :: Set String
        symbols = S.fromList (allSymbols' cl)

        quants :: [q]
        quants = allQuant' cl

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
           | otherwise                    = escape (M.singleton '\'' "prime") s

escape :: Map Char String -> String -> String
escape m = concatMap (\c -> fromMaybe [c] (M.lookup c m))

lower :: String -> String
lower = map toLower

protectedWiredIn :: Set String
protectedWiredIn = S.fromList ["app","min","$min","minrec","cf","type"]

qvarEscapes :: Map Char String
qvarEscapes = M.fromList
    [ ('\'',"prime")
    , ('!' ,"bang")
    , ('#' ,"hash")
    , ('$' ,"dollar")
    , ('%' ,"pc")
    , ('&' ,"amp")
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
prelude = M.empty
