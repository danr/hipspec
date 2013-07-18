-- | HipSpec 3.0
{-# LANGUAGE RecordWildCards #-}
module Main where

import HipSpec.Theory
import HipSpec.Translate
import HipSpec.Read
import HipSpec.Calls
import HipSpec.ParseDSL
import HipSpec.Property
import HipSpec.Plain
import HipSpec.Induction
import HipSpec.Trim
import HipSpec.ThmLib
import HipSpec.Params

import qualified Lang.Simple as S
import qualified Lang.RichToSimple as S
import Lang.ToPolyFOL (diag)

import Lang.Unfoldings
import Lang.RemoveDefault
import Lang.Uniquify
import Lang.FreeTyCons

import TyCon (isAlgTyCon)

import UniqSupply

import Control.Monad
import Control.Applicative

import Data.List (partition)

import System.Process
import Data.Maybe(catMaybes)

main :: IO ()
main = do

    params <- sanitizeParams <$> cmdArgs defParams

    var_props <- execute (file params)

    us0 <- mkSplitUniqSupply 'h'

    let not_dsl x = not $ any ($x) [isEquals, isGiven, isGivenBool, isProveBool]

        vars = filterVarSet not_dsl $
               unionVarSets (map transCalls var_props)

        (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ e)
            | v <- varSetElems vars
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter (\ x -> isAlgTyCon x && not (typeIsProp x))
                     (exprsTyCons (map snd binds))

        (am_tcs,data_thy,ty_env) = trTyCons tcs

        -- Now, split these into properties and non-properties

        simp_fns = toSimp binds

        is_prop (S.Function (_ S.::: t) _ _) =
            case res of
                S.TyCon (S.Old p) _ -> typeIsProp p
                _                   -> False

          where
            (_tvs,t')   = S.collectForalls t
            (_args,res) = S.collectArrTy t'

        (props,fns) = partition is_prop simp_fns

    -- putStrLn "\nDefinitions\n"
    -- mapM_ (putStrLn . showSimp) fns

    let am_fin = am_fns `combineArityMap` am_tcs
        (am_fns,binds_thy) = trSimpFuns am_fin fns

        thy = appThy : data_thy ++ binds_thy

        trimmer = trim thy

        try_oblig Obligation{..} = do
            let ss   = trimmer (dependencies ob_content)
                goal = ppAltErgo (sortClauses (concatMap clauses (ob_content:ss)))
                mlw = "/tmp/" ++ prop_name ob_prop ++ "_" ++ obInfoFileName ob_info ++ ".mlw"
            writeFile mlw goal
            (_exc,out,err) <- readProcessWithExitCode "alt-ergo" [mlw,"-timelimit","1","-triggers-var"] ""
            putStrLn $ mlw ++ " " ++ out ++ "\n" ++ err

        -- cls = sortClauses (concatMap clauses thy)

    -- putStrLn "\nDefinitions in clauses\n"
    -- putStrLn (ppAltErgo cls)

    putStrLn "\nProperties\n"
    case trProperties props of
        Right props' -> forM_ props' $ \ prop -> do
            print prop
            let prop' = etaExpandProp prop
            print prop'
            let coords = zipWith const [0..] (prop_vars prop')
                obs = [plain am_fin prop']
                    : catMaybes [ induction ty_env am_fin prop' (catMaybes [c1,c2])
                                | (c1,c2) <- diag (Nothing:map Just coords)
                                ]
            mapM_ (mapM_ try_oblig) obs
        Left err -> print err

