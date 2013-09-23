{-# LANGUAGE RecordWildCards, DisambiguateRecordFields, NamedFieldPuns #-}
module HipSpec.Init (processFile,SigInfo(..)) where

import Control.Monad


import Data.List (partition,union)
import Data.Void

import HipSpec.GHC.Calls
import HipSpec.Monad
import HipSpec.ParseDSL
import HipSpec.Property
import HipSpec.Read
import HipSpec.Theory
import HipSpec.Translate
import HipSpec.Params
import HipSpec.Lint
import HipSpec.Utils

import HipSpec.GHC.FreeTyCons
import HipSpec.Lang.RemoveDefault
import HipSpec.GHC.Unfoldings
import HipSpec.Lang.Uniquify

import qualified HipSpec.Lang.RichToSimple as S
import qualified HipSpec.Lang.Simple as S

import TyCon (isAlgTyCon)
import UniqSupply

import System.Exit
import System.Process
import System.FilePath

import Text.Show.Pretty

processFile :: (Maybe SigInfo -> [Property Void] -> HS a) -> IO a
processFile cont = do

    params@Params{..} <- fmap sanitizeParams (cmdArgs defParams)

    whenFlag params PrintParams $ putStrLn (ppShow params)

    EntryResult{..} <- execute params

    us0 <- mkSplitUniqSupply 'h'

    let not_dsl x = not $ any ($x) [isEquals, isGiven, isGivenBool, isProveBool]

        vars = filterVarSet not_dsl $
               unionVarSets (map (transCalls Without) prop_ids)

        (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ e)
            | v <- varSetElems vars
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter (\ x -> isAlgTyCon x && not (typeIsProp x))
                     (bindsTyCons' binds `union` extra_tcs)

        (am_tcs,data_thy,ty_env') = trTyCons tcs

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

        am_fin = am_fns `combineArityMap` am_tcs
        (am_fns,binds_thy) = trSimpFuns am_fin fns

        thy = appThy : data_thy ++ binds_thy

        cls = sortClauses (concatMap clauses thy)

        tr_props
            = sortOn prop_name
            $ either (error . show)
                     (map (etaExpandProp . generaliseProp))
                     (trProperties props)

        env = Env { theory = thy, arity_map = am_fin, ty_env = ty_env' }

    runHS params env $ do

        debugWhen PrintSimple $ "\nSimple Definitions\n" ++ unlines (map showSimp fns)

        debugWhen PrintPolyFOL $ "\nPoly FOL Definitions\n" ++ ppAltErgo cls

        debugWhen PrintProps $
            "\nProperties in Simple Definitions:\n" ++ unlines (map showSimp props) ++
            "\nProperties:\n" ++ unlines (map show tr_props)

        checkLint (lintSimple simp_fns)
        mapM_ (checkLint . lintProperty) tr_props

        whenFlag params LintPolyFOL $ liftIO $ do
            let mlw = replaceExtension file ".mlw"
            writeFile mlw (ppAltErgo cls)
            exc <- system $ "alt-ergo -type-only " ++ mlw
            case exc of
                ExitSuccess -> return ()
                ExitFailure n -> error $ "PolyFOL-linting by alt-ergo exited with exit code" ++ show n

        when (TranslateOnly `elem` debug_flags) (liftIO exitSuccess)

        cont sig_info tr_props

