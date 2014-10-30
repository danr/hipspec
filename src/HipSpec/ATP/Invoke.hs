{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns, ScopedTypeVariables #-}
module HipSpec.ATP.Invoke
    ( invokeATPs
    , InvokeEnv(..)
    , LinTheory(..)
    , InputFormat(..)
    , Result
    ) where

import Prelude hiding (mapM)
import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Workers
import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Process
import Control.Monad hiding (mapM)
import Data.Traversable (mapM)
import Control.Applicative

import Data.Maybe
import Data.Digest.Pure.SHA
import Data.ByteString.Lazy.Char8 (pack)

import HipSpec.ThmLib
import HipSpec.Property
import HipSpec.ATP.Provers
import HipSpec.ATP.Results
import HipSpec.Monad

import HipSpec.Utils.ZEncode

import System.Directory (createDirectoryIfMissing,doesFileExist,getTemporaryDirectory,removeFile)
import System.FilePath ((</>),(<.>))

import Data.Map (Map)
import qualified Data.Map as M
import HipSpec.Pretty

import Control.Exception (SomeException)
import qualified Control.Exception as E
-- GHC 7.4 has catch from both Prelude and this module, so we qualify E.catch

{-# ANN module "HLint: ignore Use camelCase" #-}

type RenameMap = Map String LogicId

data LinTheory = LinTheory RenameMap (InputFormat -> IO String)

data InvokeEnv = InvokeEnv
    { timeout         :: Double
    , store           :: Maybe FilePath
    , provers         :: [Prover]
    , processes       :: Int
    , z_encode        :: Bool
    }

type Result = (ProverName,ProverResult)

combinator :: Functor f => f (a -> b) -> a -> f b
combinator = flip (fmap . flip ($))

interpretResult :: RenameMap -> Prover -> ProcessResult -> Maybe ProverResult
interpretResult rename_map Prover{..} pr@ProcessResult{..} = excode `seq`
    case prover_process_output stdout of
        Just Proven  -> Just (Success (combinator prover_parse_lemmas stdout)
                                    (combinator (fmap uncurry prover_parse_proofs) ((rename_map M.!),stdout)))
        Nothing    | (not (null stdout) || not (null stderr)) &&
                     (excode /= (ExitFailure (-9))) -> Just (Unknown pr)
        Just Error -> Just (Unknown pr)
        _ -> Nothing

(?) :: Bool -> (a -> a) -> a -> a
True  ? f = f
False ? _ = id

filename :: InvokeEnv -> Obligation a -> (FilePath,FilePath)
filename InvokeEnv{z_encode} (Obligation Property{prop_name} info _) =
    ((z_encode ? zencode) prop_name,(z_encode ? zencode) (obInfoFileName info))

promiseProof :: InvokeEnv -> Obligation LinTheory -> Double -> Prover
             -> HS (Promise [Obligation Result])
promiseProof env@InvokeEnv{store} ob@Obligation{..} timelimit prover@Prover{..} = do

    tmp <- fmap (</> "hipspec") (liftIO getTemporaryDirectory)

    theory_str <- liftIO (lin prover_input_format)

    let sha        = showDigest (sha256 (pack theory_str))
        cache_dir  = tmp </> show prover </> take 2 sha
        cache_file = cache_dir </> drop 2 sha

    cache_exists <- liftIO (doesFileExist cache_file)

    cached cache_exists cache_dir cache_file theory_str

  where
    LinTheory rename_map lin = ob_content

    ret res = An [fmap (const (prover_name,res)) ob]

    cached True _cache_dir cache_file _theory_str = do
        content <- liftIO (readFile cache_file)
        let mk_promise s = do
                -- liftIO $ putStrLn $ cache_file ++ ": Cache exists with content: " ++ content
                return Promise
                    { spawn = return ()
                    , cancel = return ()
                    , result = return s
                    }
        length content `seq` case content of
            '1':_ -> mk_promise (ret (Success Nothing Nothing))
            _     -> mk_promise Cancelled

    cached False cache_dir cache_file theory_str = do

       let writeCache r = do
            ex <- doesFileExist cache_file
            createDirectoryIfMissing True cache_dir
            content <- if ex then liftIO (readFile cache_file) else return ""
            when (not ex || content /= "1") $ do
                let v = if r then "1" else "0"
                -- putStrLn $ cache_file ++ ": Writing cache: " ++ v
                writeFile cache_file v
                    `E.catch` \ (_ :: SomeException) -> return ()

       filepath <- liftIO $ case store of
           Nothing  -> return Nothing
           Just dir -> do
               let (path,file) = filename env ob
                   d = dir </> path
                   f = d </> completeName prover_input_format file
               createDirectoryIfMissing True d
               writeFile f theory_str
               return (Just f)

       when (prover_cannot_stdin && isNothing filepath) $ liftIO $
           putStrLn $
               "*** " ++ show prover_name ++
               " must read its input from a file, run with --output ***"

       let filepath' | prover_cannot_stdin = case filepath of
                                               Just k  -> k
                                               Nothing -> error "Run with --output"
                     | otherwise = error $
                          "Prover " ++ show prover_name ++
                          " should not open a file, but it did!"

           inputStr | prover_cannot_stdin = ""
                    | otherwise           = theory_str

       w <- getWriteMsgFun

       let callback r = do
               w . ProverResult (prop_name ob_prop) ob_info . stdout $ r
               writeCache $ case interpretResult rename_map prover r of
                   Just Success{} -> True
                   _              -> False

       promise <- length inputStr `seq` (liftIO $
           processPromiseCallback
               callback
               prover_cmd
               (prover_args filepath' timelimit) inputStr)

       let update :: PromiseResult ProcessResult -> PromiseResult [Obligation Result]
           update Cancelled = Cancelled
           update Unfinished = Unfinished
           update (An r) = case interpretResult rename_map prover r of
               Just res -> ret res
               Nothing  -> Cancelled

       return Promise
           { spawn = do
               w $ Spawning (prop_name ob_prop) ob_info
               w $ SpawningWithTheory (prop_name ob_prop) ob_info theory_str
               spawn promise
           , cancel = do
               w $ Cancelling (prop_name ob_prop) ob_info
               cancel promise
               -- writeCache False
           , result = update <$> result promise
           }

invokeATPs :: Tree (Obligation LinTheory) -> InvokeEnv -> HS [Obligation Result]
invokeATPs tree env@InvokeEnv{..}
    | null provers = return []
    | otherwise = do

        let make_promises :: Obligation LinTheory
                          -> HS (Tree (Promise [Obligation Result]))
            make_promises p = requireAny . map Leaf <$> mapM (promiseProof env p timeout) provers

        promise_tree <- join <$> mapM make_promises tree
            -- mapM over trees, but we get a tree of trees, so we need to use join

        liftIO $ workers (Just (round $ timeout * 1000 * 1000))
                         processes
                         (interleave promise_tree)

        (err,res) <- liftIO $ evalTree (any unknown . map (snd . ob_content)) promise_tree

        return $ err ++ res

