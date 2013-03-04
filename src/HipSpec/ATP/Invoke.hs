{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns, ScopedTypeVariables #-}
module HipSpec.ATP.Invoke (invokeATPs, Env(..), LinTheory(..), TheoryType(..), Result) where

import Prelude hiding (mapM)
import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Workers
import Control.Concurrent.STM.Promise.Tree
import Control.Concurrent.STM.Promise.Process
import Control.Monad hiding (mapM)
import Data.Traversable (mapM)
import Control.Applicative

import Halo.Util

import Data.List
import Data.Maybe

import qualified Data.Map as M
import Data.Map (Map)

import HipSpec.Trans.Obligation
import HipSpec.Trans.Property
import HipSpec.ATP.Provers
import HipSpec.ATP.Results
import HipSpec.Monad

import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>),(<.>))

data LinTheory = LinTheory (TheoryType -> String)

data Env = Env
    { timeout         :: Double
    , store           :: Maybe FilePath
    , provers         :: [Prover]
    , processes       :: Int
    , z_encode        :: Bool
    }

type Result = (ProverName,ProverResult)

interpretResult :: Prover -> ProcessResult -> Maybe ProverResult
interpretResult Prover{..} pr@ProcessResult{..} = excode `seq`
    case proverProcessOutput stdout of
        Just True  -> Just (Success (get_lemmas stdout))
        Just False -> Nothing
        Nothing    -> Just (Unknown pr)
  where
    get_lemmas = case proverParseLemmas of
        Just lemma_parser -> Just . lemma_parser
        Nothing           -> const Nothing


filename :: Env -> Obligation eq a -> (FilePath,FilePath)
filename Env{z_encode} (Obligation Property{propName} info _) = case info of
    Induction coords ix _ ->
        ((z_encode ? escape) propName
        ,usv coords ++ "__" ++ show ix)
    ApproxLemma coords ix _ ->
        ((z_encode ? escape) propName
        ,"approx__" ++ usv coords ++ "__" ++ show ix)
  where
    usv = intercalate "_" . map show

promiseProof :: forall eq .
                Env -> Obligation eq LinTheory -> Double -> Prover
             -> HS (Promise [Obligation eq Result])
promiseProof env@Env{store} ob@Obligation{..} timelimit prover@Prover{..} = do

    let LinTheory lin = ob_content
        theory        = lin proverTheoryType

    filepath <- liftIO $ case store of
        Nothing  -> return Nothing
        Just dir -> do
            let (path,file) = filename env ob
                ext = case proverTheoryType of
                        TPTP         -> "tptp"
                        SMT          -> "smt"
                        SMTUnsatCore -> "unsat-core" <.> "smt"
                d = dir </> path
                f = d </> file <.> ext
            createDirectoryIfMissing True d
            writeFile f theory
            return (Just f)

    when (proverCannotStdin && isNothing filepath) $ liftIO $
        putStrLn $
            "*** " ++ show proverName ++
            " must read its input from a file, run with --output ***"

    let filepath' | proverCannotStdin = case filepath of
                                            Just k  -> k
                                            Nothing -> error "Run with --output"
                  | otherwise = error $
                       "Prover " ++ show proverName ++
                       " should not open a file, but it did!"

        inputStr | proverCannotStdin = ""
                 | otherwise         = theory

    w <- getWriteMsgFun

    let callback = w . ProverResult (propName ob_prop) ob_info . stdout

    promise <- length inputStr `seq` (liftIO $
        processPromiseCallback
            callback
            proverCmd
            (proverArgs filepath' timelimit) inputStr)

    let update :: PromiseResult ProcessResult -> PromiseResult [Obligation eq Result]
        update Cancelled = Cancelled
        update Unfinished = Unfinished
        update (An r) = case interpretResult prover r of
            Just res -> An [fmap (const (proverName,res)) ob]
            Nothing  -> Cancelled

    return Promise
        { spawn = do
            w $ Spawning (propName ob_prop) ob_info
            w $ SpawningWithTheory (propName ob_prop) ob_info theory
            spawn promise
        , cancel = do
            w $ Cancelling (propName ob_prop) ob_info
            cancel promise
        , result = update <$> result promise
        }

-- TODO: make this in the HS monad and send messages

invokeATPs :: Tree (Obligation eq LinTheory) -> Env -> HS [Obligation eq Result]
invokeATPs tree env@Env{..} = do

    let make_promises :: Obligation eq LinTheory
                      -> HS (Tree (Promise [Obligation eq Result]))
        make_promises p = requireAny . map Leaf <$> mapM (promiseProof env p timeout) provers

    promise_tree <- join <$> mapM make_promises tree
        -- mapM over trees, but we get a tree of trees, so we need to use join

    liftIO $ workers (Just (round $ timeout * 1000 * 1000))
                     processes
                     (interleave promise_tree)

    (err,res) <- liftIO $ evalTree (any unknown . map (snd . ob_content)) promise_tree

    return $ err ++ res

escape :: String -> String
escape = concatMap (\c -> fromMaybe [c] (M.lookup c escapes))

escapes :: Map Char String
escapes = M.fromList $ map (uncurry (flip (,)))
    [ ("za",'@')
    , ("z1",'(')
    , ("z2",')')
    , ("zB",'}')
    , ("zC",'%')
    , ("zG",'>')
    , ("zH",'#')
    , ("zL",'<')
    , ("zR",'{')
    , ("zT",'^')
    , ("zV",'\\')
    , ("z_",'\'')
    , ("zb",'!')
    , ("zc",':')
    , ("zd",'$')
    , ("zh",'-')
    , ("zi",'|')
    , ("zl",']')
    , ("zm",',')
    , ("zn",'&')
    , ("zo",'.')
    , ("zp",'+')
    , ("zq",'?')
    , ("zr",'[')
    , ("zs",'*')
    , ("zt",'~')
    , ("zv",'/')

    , ("zz",'z')

    , ("_equals_",'=')

    , ("_",' ')
    ]
