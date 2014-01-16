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
import HipSpec.Id

import HipSpec.GHC.FreeTyCons
import HipSpec.Lang.RemoveDefault
import HipSpec.GHC.Unfoldings
import HipSpec.Lang.Uniquify

-- import qualified HipSpec.Lang.RichToSimple as S
import qualified HipSpec.Lang.Simple as S

import TyCon (isAlgTyCon)
import UniqSupply

import System.Exit
import System.Process
import System.FilePath

-- import Name(Name)
-- import Data.Set (Set)
import Text.Show.Pretty hiding (Name)
-- import HipSpec.Lang.Monomorphise hiding (Inst)
-- import HipSpec.Lang.CoreToRich (trTyCon)


processFile :: (Maybe SigInfo -> [Property Void] -> HS a) -> IO a
processFile cont = do

    params@Params{..} <- fmap sanitizeParams (cmdArgs defParams)

    whenFlag params PrintParams $ putStrLn (ppShow params)

    EntryResult{..} <- execute params

    us0 <- mkSplitUniqSupply 'h'

    let vars = filterVarSet (not . varFromPrelude) $
               unionVarSets (map (transCalls Without) prop_ids)

        (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ e)
            | v <- varSetElems vars
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter (\ x -> isAlgTyCon x && not (isPropTyCon x))
                     (bindsTyCons' binds `union` extra_tcs)

        (am_tcs,data_thy,ty_env') = trTyCons tcs

        -- Now, split these into properties and non-properties

        simp_fns :: [S.Function Id]
        simp_fns = toSimp binds

        is_prop (S.Function _ (S.Forall _ t) _ _) = isPropType t

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

        -- *** TESTING ***

{-
        data_types1 :: [S.Datatype Name]
        Right data_types1 = mapM trTyCon tcs

        bla :: Name -> S.Typed (Inst (S.Rename Name))
        bla = (S.::: S.Star) . inst . S.Old

        data_types :: [S.Datatype (S.Typed (Inst (S.Rename Name)))]
        data_types = map (fmap bla) data_types1

        bli :: S.Var Name -> S.Typed (Inst (S.Rename Name))
        bli = fmap inst

        mono_types = [ dt | dt@(S.Datatype _ [] _) <- data_types ]

        simp_fns' = map (fmap bli) simp_fns

    forM_ mono_types $ \ (S.Datatype mono_type _ _) ->
        forM_ simp_fns' $ \ (S.Function f ts _ _) -> unless (null ts) $ do
            let iv :: [(V,S.Type V)] -> [S.Type V] -> V -> V
                iv su [] y@(Inst _ _ S.::: _) = y
                iv su ts (Org x S.::: t) = (Inst x (map S.forget ts)
                                            S.::: S.substManyTys su ti
                                           )
                  where (vs,ti) = S.collectForalls t

                hr :: V -> [(V,[S.Type V])]
                hr (Inst _ ts S.::: t) = S.tyTyCons t
                hr (Org _ S.::: t)     = S.tyTyCons t

                prg_act :: (Prog V,Set (Record V))
                prg_act = instProg iv hr (data_types,simp_fns')
                            [(f,map (\ _ -> S.TyCon mono_type []) ts)]

            putStrLn $ ppShow prg_act
            -}

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

