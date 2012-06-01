{-# LANGUAGE RecordWildCards, ViewPatterns #-}
module Hip.InvokeATPs where

import Control.Concurrent
import Control.Concurrent.STM.TChan
import Control.Concurrent.STM.TVar
import Control.Monad.STM
import Control.Monad
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State

import Control.Arrow ((***),first,second)

import Data.List
import Data.Maybe

import qualified Data.Map as M
import Data.Map (Map)

import Hip.Trans.ProofDatatypes
import Hip.ResultDatatypes
import Hip.Provers
import Hip.RunProver

import System.IO.Unsafe (unsafeInterleaveIO)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))

type PropName = String

type PropIn     = PropertyMatter [PartIn]
type PartIn     = PartMatter [ParticleIn]
type ParticleIn = ParticleMatter String

type PropResult = PropertyMatter (Status,[PartResult])
type PartResult = PartMatter [ParticleResult]
type ParticleResult = ParticleMatter (ProverResult,Maybe ProverName)

statusFromPart :: PartResult -> Status
statusFromPart (Part _ (map (fst . particleMatter) -> res))
    = statusFromResults res

plainProof :: PropResult -> Bool
plainProof = any (\p -> partMethod p == Plain && statusFromPart p /= None)
           . snd . propMatter

data Env = Env { propStatuses    :: MVar (Map PropName Status)
               , propCodes       :: Map PropName String
               , reproveTheorems :: Bool
               , timeout         :: Int
               , store           :: Maybe FilePath
               , provers         :: [Prover]
               , processes       :: Int
               }

type ProveM = ReaderT Env IO

runProveM :: Env -> ProveM a -> IO a
runProveM = flip runReaderT

invokeATPs :: [PropIn] -> Env -> IO [PropResult]
invokeATPs properties env@(Env{..}) = do
    statusMVar <- newMVar M.empty
    doneMVar   <- newTVarIO False

    let codes = M.fromList [ (probName,probCode) | Property probName probCode _ <- properties ]
        env' = env { propStatuses = statusMVar, propCodes = codes }
        allParts  = [ (propName,part) | Property propName _ parts <- properties , part <- parts ]
        propParts = M.fromList [ (propName,length parts) | Property propName _ parts <- properties ]

    probChan         <- newChan
    intermediateChan <- newChan
    resChan          <- newTChanIO

    mapM_ (writeChan probChan) allParts

    workers <- replicateM processes $ forkIO (runProveM env' (worker probChan intermediateChan))

    void $ forkIO $ runProveM env' (listener intermediateChan resChan propParts workers doneMVar)

    consume resChan doneMVar
  where
    consume :: TChan PropResult -> TVar Bool -> IO [PropResult]
    consume resChan doneTVar = fix $ \loop -> unsafeInterleaveIO $ do
--      putStrLn "consuming..."
        element <- atomically $ do is_empty <- isEmptyTChan resChan
                                   done  <- readTVar doneTVar
                                   if is_empty then (if done then return Nothing else retry)
                                               else Just <$> readTChan resChan
        case element of
                Nothing -> return []
                Just e  -> (e:) <$> loop

propStatus :: PropName -> ProveM Status
propStatus propName = do
    Env{..} <- ask
    if reproveTheorems
      then return None
      else do
        statusMap <- liftIO (readMVar propStatuses)
        let status = fromMaybe None (M.lookup propName statusMap)
--        liftIO $ putStrLn $ "status on " ++ propName ++ " is " ++ show status
        return status

updatePropStatus :: PropName -> Status -> ProveM ()
updatePropStatus propName status = do
    Env{..} <- ask
    unless reproveTheorems
       (liftIO $ modifyMVar_ propStatuses (return . M.insertWith max propName status))
--    liftIO $ do putStrLn $ "updated " ++ propName ++ " to " ++ show status
--                map <- readMVar propStatuses
--                print map

type ListenerSt = (Map PropName Int,Map PropName PropResult)

-- | Listens to all the results, report if a property was proven,
--   and puts them all in a list of results
listener :: Chan (PropName,PartResult) -> TChan PropResult
         -> Map PropName Int -> [ThreadId] -> TVar Bool -> ProveM ()
listener intermediateChan resChan propParts workers doneTVar = do
    Env{..} <- ask

    let initState :: ListenerSt
        initState = (propParts,M.empty)

        process :: StateT ListenerSt ProveM ()
        process = fix $ \loop -> do
            res@(propName,part) <- liftIO (readChan intermediateChan)
            let status = statusFromPart part
            lift $ updatePropStatus propName status

            -- update map
            modify (second (uncurry updateResults res propCodes))

            -- decrement propName parts
            modify (first (M.adjust pred propName))

            left <- gets ((M.! propName) . fst)

--          liftIO $ putStrLn $ propName ++ " parts left: " ++ show left

            -- all parts are done, write on res chan and remove from the state
            when (left == 0) $ do
                liftIO . atomically . writeTChan resChan =<< gets ((M.! propName) . snd)
                modify (M.delete propName *** M.delete propName)

            -- are we finished?
            done <- gets (M.null . fst)
            unless done loop

    unless (M.null propParts) (evalStateT process initState)

    liftIO $ do -- putStrLn "All parts are done"
                mapM_ killThread workers
                atomically (writeTVar doneTVar True)
  where
    updateResults :: PropName -> PartResult -> Map PropName String
                  -> Map PropName PropResult -> Map PropName PropResult
    updateResults name partRes propCodeMap= M.alter (Just . alterer) name
      where
        alterer :: Maybe PropResult -> PropResult
        alterer m = case m of
           Nothing -> Property name (propCodeMap M.! name) (statusFromPart partRes,[partRes])
           Just (Property name' code (status,parts)) ->
                      Property name' code (statusFromPart partRes `max` status,partRes:parts)

-- | A worker. Reads the channel of parts to process, and writes to
-- the result channel. Skips doing the rest of the particles if one
-- fails, or if the property is proved elsewhere.
worker :: Chan (PropName,PartIn) -> Chan (PropName,PartResult) -> ProveM ()
worker partChan resChan = forever $ do
    (propName,Part partMethod particles) <- liftIO (readChan partChan)

--  liftIO $ putStrLn $ "Working on " ++ propName ++ "."

    env@(Env{..}) <- ask

    let unnecessary Theorem       = True
        unnecessary _             = False

        processParticle :: ParticleIn -> StateT Bool ProveM ParticleResult
        processParticle (Particle particleDesc tptp) = do
            stop <- get
            if stop then return (Particle particleDesc (Failure,Nothing)) else do
                resvar <- liftIO newEmptyMVar

                let filename = propName </>
                               intercalate "_" [proofMethodFile partMethod,particleDesc]
                               ++ ".tptp"

                length tptp `seq`
                    (void . liftIO . forkIO
                          . runProveM env . runProvers filename tptp $ resvar)

                case store of
                   Nothing  -> return ()
                   Just dir -> liftIO $ do
                       createDirectoryIfMissing True (dir ++ propName)
                       writeFile (dir ++ filename) tptp

                (res,maybeProver) <- liftIO (takeMVar resvar)
                provedElsewhere <- unnecessary <$> lift (propStatus propName)

                when (not (success res) || provedElsewhere) (put True)
                return (Particle particleDesc (res,maybeProver))

    provedElsewhere <- unnecessary <$> propStatus propName

    res <- evalStateT (mapM processParticle particles) provedElsewhere

    liftIO (writeChan resChan (propName,Part partMethod res))

--  liftIO $ putStrLn $ "Finished " ++ propName ++ "."

runProvers :: FilePath -> String
           -> MVar (ProverResult,Maybe ProverName) -> ProveM ()
runProvers filename str res = do
    Env{..} <- ask
    liftIO . putMVar res =<< go provers
  where
    go (p:ps) = do t <- asks timeout
                   r <- liftIO $ runProver filename p str t
                   case r of
                      Failure   -> go ps
                      _         -> return (r,Just (proverName p))
    go []     = return (Failure,Nothing)


