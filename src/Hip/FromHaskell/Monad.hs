{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleContexts,TemplateHaskell #-}
module Hip.FromHaskell.Monad where

import Hip.Trans.Core as C
import Hip.Trans.Constructors (bottomName)
import Hip.Messages

import Language.Haskell.Exts as H hiding (Name,Decl,binds)

import Control.Applicative
import Control.Monad.Error
import Control.Monad.RWS hiding (gets,modify,local,asks)
import Data.Label.PureM

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)

import Data.Label (mkLabels)
import Data.Either (partitionEithers)
import Data.List (intercalate)

data St = St { _namesupply :: [Int]
             , _binds      :: Map Name (Name,[Name])
              -- ^ An identifier to its scoped name and free vars
             , _scope      :: Set Name
             , _datatypes  :: Set Name
              -- ^ An identifier in scope
             }
$(mkLabels [''St])

data Env = Env { _scopeName :: [String] }
$(mkLabels [''Env])

initSt :: St
initSt = St { _namesupply = [0..]
            , _binds      = M.fromList [("undefined",(bottomName,[]))]
            , _scope      = S.fromList ["prove","proveBool","=:=","=/="]
            , _datatypes  = S.empty
            }

regData :: Name -> FH ()
regData = modify datatypes . S.insert

getDatas :: FH [Name]
getDatas = S.toList <$> gets datatypes

initEnv :: Env
initEnv = Env { _scopeName = [] }

newtype FH a = FH (ErrorT String (RWS Env [Either Msg Decl] St) a)
  deriving(Functor,Applicative,Monad
          ,MonadWriter [Either Msg Decl]
          ,MonadReader Env
          ,MonadState St
          ,MonadError String)

runFH :: FH () -> (Either String [Decl],[Msg])
runFH (FH m) = case evalRWS (runErrorT m) initEnv initSt of
  (r,w) -> let (msgs,decls) = partitionEithers w
           in  (case r of
                   Right () -> Right decls
                   Left err -> Left err
               ,msgs)

localScopeName :: Name -> FH a -> FH a
localScopeName n = local scopeName (n:)

localBindScope :: FH a -> FH a
localBindScope m = do
  bs <- gets binds
  sc <- gets scope
  r <- m
  puts binds bs
  puts scope sc
  return r

addToScope :: Name -> FH ()
addToScope = modify scope . S.insert

removeFromScope :: Name -> FH ()
removeFromScope n = do
  modify scope (S.delete n)
  modify binds (M.delete n)

inScope :: Name -> FH Bool
inScope n = S.member n <$> gets scope

namesInScope :: FH [Either Name Name]
namesInScope = liftM2 (++) (map Left . M.keys <$> gets binds)
                           (map Right . S.toList <$> gets scope)

addBind :: Name -> Name -> [Name] -> FH ()
addBind fname scopedfname args
    | fname == scopedfname && not (null args) =
        fatal $ "Scope error, " ++ fname ++ " uses: " ++ unwords args
    | otherwise = do modify binds (M.insert fname (scopedfname,args))
                     debug $ "addBind: " ++ fname ++ " to " ++ scopedfname
                             ++ " with args " ++ unwords args

lookupBind :: Name -> FH (Maybe (Name,[Name]))
lookupBind n = M.lookup n <$> gets binds

scopePrefix :: Name -> FH Name
scopePrefix n = do
  s <- asks scopeName
  if null s then return n
            else do u <- newUnique
                    let delim = "."
                    return ({- intercalate delim (reverse s) ++ delim ++ -}
                            n ++ delim ++ show u)

newUnique :: FH Int
newUnique = do
  x:xs <- gets namesupply
  puts namesupply xs
  return x

wildName :: FH Name
wildName = (("wild."++) . show) <$> newUnique

_write :: Msg -> FH ()
_write = tell . return . Left

warn :: String -> FH ()
warn = _write . warnMsg

fatal :: String -> FH a
fatal = throwError . ("Fatal: " ++)

decl :: Decl -> FH ()
decl = tell . return . Right

debug :: String -> FH ()
debug = _write . dbfhMsg