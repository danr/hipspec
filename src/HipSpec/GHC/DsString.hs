-- This file is mainly a copy of excepts of HscMain from GHC.  The problem
-- is that runStmt does not return ds_expr, which is what we need.
--
-- THE LICENCE OF GHC IS BSD SO THIS APPLIES TO THIS FILE TOO
module HipSpec.GHC.DsString (dsExpr) where

import Bag
import CoreSyn
import Desugar
import DynFlags
import ErrUtils
import Exception
import FastString hiding (buf)
import HscTypes
import HsSyn
import Lexer hiding (dflags,loc)
import Outputable
import Parser
import PrelNames
import RdrName
import SrcLoc
import StringBuffer hiding (buf)
import TcRnDriver
import TcRnMonad
import CoreSubst (simpleOptExpr)

import GhcMonad (GhcMonad,getSession)

import Control.Monad

-- call with "let foo = ..." (as in ghci)
dsExpr :: GhcMonad m => String -> m (Maybe CoreBind)
dsExpr s = do
    hsc_env <- getSession
    liftIO $ hscExpr hsc_env s "<interactive>" 1

hscExpr :: HscEnv -> String -> String -> Int -> IO (Maybe CoreBind)
hscExpr hsc_env0 stmt source linenumber =
 runInteractiveHsc hsc_env0 $ do
    hsc_env <- getHscEnv
    maybe_stmt <- hscParseStmtWithLocation source linenumber stmt
    case maybe_stmt of
        Nothing -> return Nothing

        Just parsed_stmt -> do
            let icntxt   = hsc_IC hsc_env
                rdr_env  = ic_rn_gbl_env icntxt
                type_env = mkTypeEnvWithImplicits (ic_tythings icntxt)
                _src_span = srcLocSpan interactiveSrcLoc

            -- Rename and typecheck it
            -- Here we lift the stmt into the IO monad, see Note
            -- [Interactively-bound Ids in GHCi] in TcRnDriver
            (_ids, tc_expr, _fix_env) <- ioMsgMaybe $ tcRnStmt hsc_env icntxt parsed_stmt

            -- Desugar it
            ds_expr <- ioMsgMaybe $
                           deSugarExpr hsc_env iNTERACTIVE rdr_env type_env tc_expr

            handleWarnings

            --      let foo = ...
            -- Is desugared to
            --      letrec foo = ... in unsafeCoerceInto <IO ()>,
            -- And we only want the binder. We run simpleOptExpr since the
            -- binder usually contains a nested letrec.
            case ds_expr of
                Let (Rec [(v,e)]) _ -> do
                    let e' = simpleOptExpr e
                    return (Just (Rec [(v,e')]))
                _ -> return Nothing


-- The Hsc monad: Passing an enviornment and warning state

newtype Hsc a = Hsc (HscEnv -> WarningMessages -> IO (a, WarningMessages))

instance Monad Hsc where
    return a    = Hsc $ \_ w -> return (a, w)
    Hsc m >>= k = Hsc $ \e w -> do (a, w1) <- m e w
                                   case k a of
                                       Hsc k' -> k' e w1

instance MonadIO Hsc where
    liftIO io = Hsc $ \_ w -> do a <- io; return (a, w)

instance Functor Hsc where
    fmap f m = m >>= \a -> return $ f a

runHsc :: HscEnv -> Hsc a -> IO a
runHsc hsc_env (Hsc hsc) = do
    (a, w) <- hsc hsc_env emptyBag
    printOrThrowWarnings (hsc_dflags hsc_env) w
    return a

runInteractiveHsc :: HscEnv -> Hsc a -> IO a
runInteractiveHsc hsc_env =
  runHsc (hsc_env { hsc_dflags = ic_dflags (hsc_IC hsc_env) })


getWarnings :: Hsc WarningMessages
getWarnings = Hsc $ \_ w -> return (w, w)

clearWarnings :: Hsc ()
clearWarnings = Hsc $ \_ _ -> return ((), emptyBag)

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)

getHscEnv :: Hsc HscEnv
getHscEnv = Hsc $ \e w -> return (e, w)

instance HasDynFlags Hsc where
    getDynFlags = Hsc $ \e w -> return (hsc_dflags e, w)

handleWarnings :: Hsc ()
handleWarnings = do
    dflags <- getDynFlags
    w <- getWarnings
    liftIO $ printOrThrowWarnings dflags w
    clearWarnings

-- | log warning in the monad, and if there are errors then
-- throw a SourceError exception.
logWarningsReportErrors :: Messages -> Hsc ()
logWarningsReportErrors (warns,errs) = do
    logWarnings warns
    when (not $ isEmptyBag errs) $ throwErrors errs

-- | Throw some errors.
throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr

-- | Deal with errors and warnings returned by a compilation step
--
-- In order to reduce dependencies to other parts of the compiler, functions
-- outside the "main" parts of GHC return warnings and errors as a parameter
-- and signal success via by wrapping the result in a 'Maybe' type. This
-- function logs the returned warnings and propagates errors as exceptions
-- (of type 'SourceError').
--
-- This function assumes the following invariants:
--
--  1. If the second result indicates success (is of the form 'Just x'),
--     there must be no error messages in the first result.
--
--  2. If there are no error messages, but the second result indicates failure
--     there should be warnings in the first result. That is, if the action
--     failed, it must have been due to the warnings (i.e., @-Werror@).
ioMsgMaybe :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe ioA = do
    ((warns,errs), mb_r) <- liftIO ioA
    logWarnings warns
    case mb_r of
        Nothing -> throwErrors errs
        Just r  -> return r

hscParseStmtWithLocation :: String -> Int -> String
                         -> Hsc (Maybe (LStmt RdrName))
hscParseStmtWithLocation source linenumber stmt =
    hscParseThingWithLocation source linenumber parseStmt stmt

hscParseThingWithLocation :: Outputable thing => String -> Int
                          -> Lexer.P thing -> String -> Hsc thing
hscParseThingWithLocation source linenumber parser str
  = do
    dflags <- getDynFlags
    liftIO $ showPass dflags "Parser"

    let buf = stringToStringBuffer str
        loc = mkRealSrcLoc (fsLit source) linenumber 1

    case unP parser (mkPState dflags buf loc) of
        PFailed span' err -> do
            let msg = mkPlainErrMsg dflags span' err
            throwErrors $ unitBag msg

        POk pst thing -> do
            logWarningsReportErrors (getMessages pst)
            liftIO $ dumpIfSet_dyn dflags Opt_D_dump_parsed "Parser" (ppr thing)
            return thing
