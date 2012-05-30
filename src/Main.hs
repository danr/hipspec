{-# LANGUAGE RecordWildCards,ViewPatterns #-}
module Main where

import Hip.Trans.MakeProofs
import Hip.Trans.Theory
import Hip.Trans.Property

import Hip.Params
import Hip.Trans.SrcRep

import Hip.InvokeATPs
import Hip.Trans.ProofDatatypes (propMatter)
import qualified Hip.Trans.ProofDatatypes as PD
import Hip.ResultDatatypes
import Hip.Provers

import Halt.Lift
import Halt.Conf
import Halt.Monad
import Halt.Trans
import Halt.Entry

import Data.List
import Data.Maybe

import Control.Monad
import Control.Applicative
import Control.Arrow ((***))

import System.Console.CmdArgs hiding (summary)
import System.Exit
import System.FilePath

import BasicTypes
import CoreSyn
import GHC
import HscTypes
import UniqSupply

import TysWiredIn

removeMain :: [CoreBind] -> [CoreBind]
removeMain = filter (not . remove)
  where
    remove (NonRec x _) | isMain x = True
    remove _ = False

main :: IO ()
main = do
  params@Params{..} <- cmdArgs defParams

  when (null files) $ do
      putStrLn "No input files. Run with --help to see possible flags"
      exitFailure
  whenLoud $ do putStrLn $ "Verbose output, files: " ++ unwords files
                putStrLn $ "Param: " ++ showParams params

  forM_ files $ \(dropExtension -> file) -> do
      when (file /= head files) $ putStrLn ""
      unless (null files) $ putStrLn $ file ++ ":"
      -- Parse either Haskell or Core

      (modguts,dflags) <- desugar (DesugarConf { debug_float_out = False
                                               , core2core_pass  = True
                                               }) file

      let unlifted_program = removeMain . mg_binds $ modguts

      us <- mkSplitUniqSupply 'f'

      ((lifted_program,_msgs_lift),_us) <- (`caseLetLift` us)
                                       <$> lambdaLift dflags unlifted_program

      let isPropBinder (NonRec x _) | isPropType x = True
          isPropBinder _ = False

          (core_props,core_defns) = partition isPropBinder lifted_program

          ty_cons :: [TyCon]
          ty_cons = mg_tcs modguts

          ty_cons_with_builtin :: [TyCon]
          ty_cons_with_builtin = listTyCon : boolTyCon : unitTyCon
                               : map (tupleTyCon BoxedTuple) [2..2]
                                 -- ^ choice: only tuples of size 2 supported!!
                               ++ ty_cons

          halt_conf :: HaltConf
          halt_conf  = sanitizeConf $ HaltConf
                          { use_min      = False
                          , use_cf       = False
                          , unr_and_bad  = False
                          }

          halt_env = mkEnv halt_conf ty_cons_with_builtin core_defns

          (data_axioms,def_axioms,_msgs_trans)
              = translate halt_env ty_cons_with_builtin core_defns

          theory = Theory data_axioms def_axioms (error "Theory.thyTyEnv")

          props = inconsistentProp : mapMaybe trProperty core_props

      {-
      forM_ props $ \prop -> do let Prop{..} = prop
                                putStrLn $ propName ++ ": "
                                        ++ showExpr proplhs ++ " = "
                                        ++ showExpr proprhs
      -}

      (unproved,proved) <- parLoop halt_env params theory props []

      printInfo unproved proved

      return ()

  return ()

printInfo :: [Prop] -> [Prop] -> IO ()
printInfo unproved proved = do
    let pr xs | null xs   = "(none)"
              | otherwise = unwords (map propName xs)
    putStrLn ("Proved: " ++ pr proved)
    putStrLn ("Unproved: " ++ pr unproved)
    putStrLn (show (length proved) ++ "/" ++ show (length (proved ++ unproved)))


-- | Try to prove some properties in a theory, given some lemmas
tryProve :: HaltEnv -> Params -> [Prop] -> Theory -> [Prop] -> IO [(Prop,Bool)]
tryProve halt_env params@(Params{..}) props thy lemmas = do
    let env = Env { reproveTheorems = reprove
                  , timeout         = timeout
                  , store           = output
                  , provers         = proversFromString provers
                  , processes       = processes
                  , propStatuses    = error "main env propStatuses"
                  , propCodes       = error "main env propCodes"
                  }

        (properties,_msgs) = runHaltM halt_env
                           . mapM (\prop -> theoryToInvocations params thy prop lemmas)
                           $ props

    res <- invokeATPs properties env

    forM res $ \property -> do
        let proved = fst (propMatter property) /= None
        when proved (putStrLn $ "Proved " ++ PD.propName property ++ ".")
        return (fromMaybe (error "tryProve: lost")
                          (find ((PD.propName property ==) . propName) props)
               ,proved)

parLoop :: HaltEnv -> Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
parLoop halt_env params thy props lemmas = do
    (proved,unproved) <-  (map fst *** map fst) . partition snd
                      <$> tryProve halt_env params props thy lemmas
    if null proved then return (props,lemmas)
                   else do putStrLn $ "Adding " ++ show (length proved) ++ " lemmas: " ++ unwords (map propName proved)
                           parLoop halt_env params thy unproved (proved ++ lemmas)

