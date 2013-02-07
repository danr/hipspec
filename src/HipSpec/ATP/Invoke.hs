{-# LANGUAGE RecordWildCards, ViewPatterns #-}
module HipSpec.ATP.Invoke where

import Prelude hiding (mapM)
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Workers
import Control.Concurrent.STM.Promise.Tree
import Control.Monad hiding (mapM)
import Data.Traversable (mapM)
import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State hiding (mapM)

import Halo.Util

import Control.Arrow ((***),first,second)

import Data.List
import Data.Maybe

import qualified Data.Map as M
import Data.Map (Map)

import HipSpec.Trans.Property
import HipSpec.Trans.ProofDatatypes
-- import HipSpec.ATP.Results
import HipSpec.ATP.Provers
-- import HipSpec.ATP.RunProver

import Halo.Util ((?))

import System.IO.Unsafe (unsafeInterleaveIO)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))


import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Process


data Env = Env
    { timeout         :: Int
    , store           :: Maybe FilePath
    , provers         :: [Prover]
    , processes       :: Int
    , z_encode        :: Bool
    }

type ProveM = ReaderT Env IO

{-
statusFromPart :: PartResult -> Status
statusFromPart (Part _ (map (fst . particleMatter) -> res))
    = statusFromResults res
    -}

{-
interpretResult :: Prover -> ProcessResult -> ProverResult
interpretResult Prover{..} pr@ProcessResult{..} = flip (,) proverName $
    case proverProcessOutput stdout of
        s@Success{} -> case proverParseLemmas of
            Just lemma_parser -> s { successLemmas = lemma_parser stdout }
            Nothing -> s
        Failure -> Failure
        Unknown _ -> Unknown (show pr)
        -}

type ProverResult = ()


interpretResult :: ProcessResult -> ProverResult
interpretResult ProcessResult{..} = excode `seq` ()

promiseProof :: Property String -> Int -> Prover -> IO (Promise [Property ProverResult])
promiseProof (Property p inputStr) timelimit Prover{..} = do

    {-
    let filename = "apabepa"  -- calculate this from a hash of input string,
                              -- or get it from some other information
                              -- (property name, induction step ish ish)


    when proverCannotStdin $ do
        exists <- doesFileExist filename
        unless exists $ putStrLn $
            "*** " ++ filename ++ " using " ++  show proverName ++
            " must read its input from a file, run with --output ***"
            -}

    when proverCannotStdin $ error "Cannot use non-stdin provers at the moment!"

    let filename = error "filename!"

    let inputStr' | proverCannotStdin = ""
                  | otherwise         = inputStr

    promise <- processPromise proverCmd (proverArgs filename timelimit) inputStr'

    return Promise
        { spawn = do
            -- putStrLn $ "Spawning " ++ propName p ++ ": "
            -- putStrLn inputStr
            spawn promise
        , cancel = do
            -- putStrLn $ "Cancelling " ++ propName p ++ "!"
            cancel promise
        , result = fmap ((:[]) . Property p . interpretResult) <$> result promise
        }

invokeATPs :: Tree (Property String) -> Env -> IO [Property ProverResult]
invokeATPs tree env@Env{..} = do

    {- putStrLn (showTree $ fmap (propName . prop_prop) tree)

    void $ flip mapM tree $ \ (Property prop s) -> do
        putStrLn $ propName prop ++ ": " ++ "\n" ++ s
        putStrLn "\n"
        -}

    let make_promises :: Property String -> IO (Tree (Promise [Property ProverResult]))
        make_promises p = requireAny . map Leaf <$> mapM (promiseProof p timeout) provers

    promise_tree <- join <$> mapM make_promises tree
        -- ^ mapM over trees, but we get a tree of trees, so we need to use join

    workers (Just (timeout * 1000 * 1000)) processes (interleave promise_tree)

    res <- evalTree promise_tree

    -- print res

    return $ case res of
        Nothing    -> []
        Just props -> nubSortedOn (propName . prop_prop) props
            -- ^ Returns what was proved, but with no information how

{-

    {- -- old filename stuff:
            let almost_filename = proofMethodFile method ++ "_" ++ desc ++ ".tptp"

            filename <- case store of
                Nothing  -> return almost_filename
                Just dir -> liftIO $ do
                    let dirname  = (z_encode ? escape) propName
                        filename = dir </> dirname </> almost_filename
                    createDirectoryIfMissing True (dir </> dirname)
                    writeFile filename tptp
                    return filename
    -}

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
    -}
