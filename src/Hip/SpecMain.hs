{-# LANGUAGE RecordWildCards #-}
module Main where

import Hip.Util
import Hip.Trans.MakeTheory
import Hip.Trans.Theory
import Hip.Messages
import Hip.Params
import Hip.Trans.Parser
import Hip.Trans.Core
import Hip.Trans.Pretty
import Hip.FromHaskell.FromHaskell
import Hip.Trans.MakeProofs
import Hip.InvokeATPs
import Hip.Trans.ProofDatatypes (propMatter)
import qualified Hip.Trans.ProofDatatypes as PD
import Hip.ResultDatatypes
import Hip.Provers

import Language.TPTP.Pretty

import Data.List
import Data.Maybe

import Control.Monad
import Control.Applicative
import Control.Arrow ((***),(&&&),second)

import System.Console.CmdArgs hiding (summary)
import System.Exit (exitFailure,exitSuccess)

main :: IO ()
main = do
  params@Params{..} <- cmdArgs defParams

  when (null files) $ do
      putStrLn "No input files. Run with --help to see possible flags"
      exitFailure
  whenLoud $ do putStrLn $ "Verbose output, files: " ++ unwords files
                putStrLn $ "Param: " ++ showParams params

  forM_ files $ \file -> do
      when (file /= head files) $ putStrLn ""
      unless (null files) $ putStrLn $ file ++ ":"
      -- Parse either Haskell or Core
      (eitherds,hsdebug) <- if "hs" `isSuffixOf` file
                                then parseHaskell <$> readFile file
                                else flip (,) []  <$> parseFile file
      (err,ds) <- case eitherds of
                        Left  estr -> putStrLn estr >> return (True,error estr)
                        Right ds'  -> return (False,ds')
      unless err $ do
        -- Output debug of translation
        when dbfh $ do
          putStrLn "Translating from Haskell..."
          mapM_ print (filter (sourceIs FromHaskell) hsdebug)
          putStrLn "Translation from Haskell translation complete."
        -- Output warnings of translation
        when warnings $ mapM_ print (filter isWarning hsdebug)
        -- Output Core and terminate
        when core $ do mapM_ (putStrLn . prettyCore) ds
                       exitSuccess
        let (theory,props,msgs) = makeTheory params ds

         -- Verbose output
        when dbfol $ mapM_ print (filter (sourceIs Trans) msgs)

        -- Warnings
        when warnings $ mapM_ print (filter isWarning msgs)

{-
        forM props $ \(Prop{..}) -> do putStrLn propName
                                       putStrLn (show proplhs ++ " = " ++ show proprhs)
                                       putStrLn (intercalate "," (zipWith (\v t -> v ++ " :: " ++ show t) propVars (argsTypes propType)))
                                       putStrLn (show propVars)
                                       putStrLn (show propType)
                                       putStrLn propRepr
                                       putStrLn ""
-}

        let props' = inconsistentProp : props

        (unproved,proved) <- parLoop params theory props' []
                          {- proveLoop -}

        printInfo unproved proved

        return ()

--        print theory
--
--        print props
--
--        putStrLn "--[TPTP]--"
--
--        mapM_ (putStrLn . prettyTPTP . funcTPTP) (thyFuns theory)

  return ()

printInfo :: [Prop] -> [Prop] -> IO ()
printInfo unproved proved = do
    let pr xs | null xs   = "(none)"
              | otherwise = unwords (map propName xs)
    putStrLn ("Proved: " ++ pr proved)
    putStrLn ("Unproved: " ++ pr unproved)
    putStrLn (show (length proved) ++ "/" ++ show (length (proved ++ unproved)))


-- | Try to prove some properties in a theory, given some lemmas
tryProve :: Params -> [Prop] -> Theory -> [Prop] -> IO [(Prop,Bool)]
tryProve params@(Params{..}) props thy lemmas = do
    let env = Env { reproveTheorems = reprove
                  , timeout         = timeout
                  , store           = output
                  , provers         = proversFromString provers
                  , processes       = processes
                  , propStatuses    = error "main env propStatuses"
                  , propCodes       = error "main env propCodes"
                  }

        (properties,msgs) = second concat
                          . unzip
                          . map (\prop -> theoryToInvocations params thy prop lemmas)
                          $ props

    when dbproof $ mapM_ print (filter (sourceIs MakeProof) msgs)

    when warnings $ mapM_ print (filter isWarning msgs)

    res <- invokeATPs properties env

    forM res $ \property -> do
        let proved = fst (propMatter property) /= None
        when proved (putStrLn $ "Proved " ++ PD.propName property ++ ".")
        return (fromMaybe (error "tryProve: lost")
                          (find ((PD.propName property ==) . propName) props)
               ,proved)

proveLoop :: Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
proveLoop params thy props lemmas = do
   new <- forFind (inspect props) $ \(p,ps) -> snd . head <$> tryProve params [p] thy lemmas
   case new of
     -- Property p was proved and ps are still left to prove
     Just (p,ps) -> do putStrLn ("Proved " ++ propName p ++ ": " ++ propRepr p ++ ".")
                       proveLoop params thy ps (p:lemmas)
     -- No property was proved, return the unproved properties and the proved ones
     Nothing     -> return (props,lemmas)

parLoop :: Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
parLoop params thy props lemmas = do
    (proved,unproved) <-  (map fst *** map fst) . partition snd
                      <$> tryProve params props thy lemmas
    if null proved then return (props,lemmas)
                   else do putStrLn $ "Adding " ++ show (length proved) ++ " lemmas: " ++ unwords (map propName proved)
                           parLoop params thy unproved (proved ++ lemmas)

