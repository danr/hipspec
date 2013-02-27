{-# LANGUAGE DeriveGeneric #-}
module HipSpec.Messages where

import Data.Aeson
import GHC.Generics
import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Data.Time.Clock
import Numeric

data Msg
    = Started
    | FileProcessed
    | QuickSpecDone  { classes :: Int, eqs :: Int }
    | StartingUserLemmas
    | ExploredTheory { equations :: [String] }
    | Finished       { proved :: [String], unproved :: [String], qs_proved :: [String], qs_unproved :: [String] }
    | Discard        { discarded :: [String] }
    | Candidates     { candidates :: [String] }
    | InductiveProof { prop_name :: String, lemmas :: [String] }
    | PlainProof     { prop_name :: String, lemmas :: [String] }
    | FailedProof    { prop_name :: String }
  deriving (Eq, Ord, Show, Generic)

instance ToJSON Msg

-- GHC 7.4.1 STM does not have modifyTVar
modTVar :: TVar a -> (a -> a) -> STM ()
modTVar v f = do
    x <- readTVar v
    writeTVar v (f x)

mkWriter :: IO (Msg -> IO (), IO [(Double,Msg)])
mkWriter = do

    t0 <- getCurrentTime

    msgs <- newTVarIO []

    let obtain = fmap reverse $ atomically $ readTVar msgs

        write m = do
            t1 <- getCurrentTime
            let t :: Double
                t = fromRat (toRational (diffUTCTime t1 t0))
            atomically $ modTVar msgs ((t,m):)

    return (write,obtain)

