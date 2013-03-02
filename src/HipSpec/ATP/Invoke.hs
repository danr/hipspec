{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns, ScopedTypeVariables #-}
module HipSpec.ATP.Invoke (invokeATPs, Env(..), LinTheory(..), TheoryType(..)) where

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
    , lemma_lookup    :: Int -> Maybe String
    , store           :: Maybe FilePath
    , provers         :: [Prover]
    , processes       :: Int
    , z_encode        :: Bool
    }

type Result = (ProverName,ProverResult)

interpretResult :: Env  -> Prover -> ProcessResult -> ProverResult
interpretResult Env{lemma_lookup} Prover{..} pr@ProcessResult{..} = excode `seq`
    case proverProcessOutput stdout of
        s@Success{} -> case proverParseLemmas of
            Just lemma_parser -> s
                { successLemmas = Just . mapMaybe lemma_lookup . lemma_parser $ stdout }
            Nothing -> s
        Failure -> Failure
        Unknown _ -> Unknown (show pr)

filename :: Env -> Obligation eq (Proof a) -> (FilePath,FilePath)
filename Env{z_encode} (Obligation Property{propName} p) = case p of
    Induction coords ix _ _ ->
        ((z_encode ? escape) propName
        ,usv coords ++ "__" ++ show ix)
  where
    usv = intercalate "_" . map show

promiseProof :: forall eq .
                Env -> Obligation eq (Proof LinTheory) -> Double -> Prover
             -> HS (Promise [Obligation eq (Proof Result)])
promiseProof env@Env{store} ob@(Obligation p proof) timelimit prover@Prover{..} = do

    let LinTheory lin = proof_content proof
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

    let simp = toSimple proof

        callback = w . ProverResult (propName p) simp . stdout

    promise <- length inputStr `seq` (liftIO $
        processPromiseCallback
            callback
            proverCmd
            (proverArgs filepath' timelimit) inputStr)

    let update :: ProcessResult -> [Obligation eq (Proof Result)]
        update r = [fmap (fmap (const $ res)) ob]
          where res = (proverName,interpretResult env prover r)

    return Promise
        { spawn = do
            w $ Spawning (propName p) simp
            w $ SpawningWithTheory (propName p) simp theory
            spawn promise
        , cancel = do
            w $ Cancelling (propName p) simp
            cancel promise
        , result = fmap update <$> result promise
        }

-- TODO: make this in the HS monad and send messages

invokeATPs :: Tree (Obligation eq (Proof LinTheory)) -> Env -> HS [Obligation eq (Proof Result)]
invokeATPs tree env@Env{..} = do

    {- putStrLn (showTree $ fmap (propName . prop_prop) tree)

    void $ flip mapM tree $ \ (Obligation prop s) -> do
        putStrLn $ propName prop ++ ": " ++ "\n" ++ s
        putStrLn "\n"
        -}

    let make_promises :: Obligation eq (Proof LinTheory)
                      -> HS (Tree (Promise [Obligation eq (Proof Result)]))
        make_promises p = requireAny . map Leaf <$> mapM (promiseProof env p timeout) provers

    promise_tree <- join <$> mapM make_promises tree
        -- mapM over trees, but we get a tree of trees, so we need to use join

    liftIO $ workers (Just (round $ timeout * 1000 * 1000))
                     processes
                     (interleave promise_tree)

    res <- liftIO $ evalTree (any unknown . map (snd . proof_content . ob_content))
                             promise_tree

    -- print res

    return $ case res of
        Nothing    -> []
        Just props -> props

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
