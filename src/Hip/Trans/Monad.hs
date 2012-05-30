{-# LANGUAGE GeneralizedNewtypeDeriving,
             TemplateHaskell,
             TypeOperators,
             ParallelListComp,
             RecordWildCards,
             FlexibleContexts #-}
module Hip.Trans.Monad
       (TM()
       ,runTM
       ,write
       ,warn
       ,wdproof
       ,writeDelimiter
       ,indented
       ,getEnv
       ,popMsgs
       ,returnWithDebug
       ,locally
       ,Bound(..)
       ,popQuantified
       ,boundCon
       ,bindMeQuantPlease
       ,lookupName
       ,lookupArity
       ,lookupProj
       ,lookupType
       ,lookupConstructors
       ,forallUnbound
       ,skolemize
       ,skolemFun
       ,addIndirection
       ,makeFunPtrName
       ,addTypes
       ,addFuns
       ,addCons
       ,useFunPtr
       ,registerFunPtr
       ,getUsedFunPtrs
       ,appFold
       ,envStDecls
       ) where

import Prelude hiding ((.),id)
import Control.Category
import Data.Label (mkLabels)
import Data.Label.PureM

import Hip.Trans.Core
import Hip.Trans.Pretty
import Hip.Trans.Constructors
import Hip.Trans.ProofDatatypes
import Hip.Trans.Names as N
import Hip.Messages
import Hip.Util (isOp,putEither)
import Hip.Params

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

import Control.Applicative
import Control.Monad
import Control.Monad.State hiding (gets,modify)

import Data.Either (partitionEithers)
import Data.Maybe
import Data.List
import Data.Char

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

-- | The TM monad.
--
--   Used to be a RWS, but for convenience everything is in State,
--   even debug output to easier pair it up with accompanying code
--
--   The state capabilities are kept abstract
newtype TM a = TM { unTM :: State St a }
  deriving (Functor,Applicative,Monad)

-- | Runs a computation in an empty environment, with an empty state.
--   The computation's result is returned with the updated state.
runTM :: Params -> TM a -> a
runTM params (TM m) = evalState m (initSt params)

data Bound = QuantVar    { quantVar  :: VarName }
           | FunVar      { boundName :: FunName }
           | ConVar      { boundName :: FunName }
           | Indirection { indExpr   :: Expr    }
  deriving(Eq,Ord,Show)

-- | Is a bound variable a constructor?
boundCon :: Bound -> Bool
boundCon (ConVar _) = True
boundCon _          = False

-- | The empty state
initSt :: Params -> St
initSt p = St { _arities     = M.empty
              , _conProj     = M.empty
              , _conFam      = M.empty
              , _datatypes   = []
              , _usedFunPtrs = S.empty
              , _boundNames  = M.empty
              , _quantified  = S.empty
              , _debug       = []
              , _debugIndent = 0
              , _namesupply  = [ show x | x <- [(0 :: Integer)..] ]
              , _types       = M.empty
              , _params      = p
              }

data St = St { _arities     :: Map Name Int
               -- ^ Arity of functions and constructors
             , _conProj     :: Map Name [Name]
               -- ^ Projection functions for constructors
             , _conFam      :: Map Name [Name]
               -- ^ The constructors for a datatype
             , _datatypes   :: [[(Name,Int)]]
               -- ^ The datatypes in the program
             , _usedFunPtrs :: Set (Name,Int)
               -- ^ Which functions we need to produce ptr conversions for, and what
               --   arity they had at the time
             , _boundNames  :: Map Name Bound
               -- ^ TPTP name of funs/costr and quantified variables
             , _quantified  :: Set (Either VarName VarName)
               -- ^ Variables to quantify over.
               --   Left: Existential quantification,
               --   Right: Universal quantification
             , _debug       :: [Msg]
               -- ^ Debug messages
             , _debugIndent :: Int
               -- ^ Indentation depth for debug messages
             , _namesupply  :: [Name]
               -- ^ Namesupply, currently only used to rename infix operators
             , _types       :: Map Name Type
               -- ^ Types of functions and constructors
             , _params      :: Params
               -- ^ Parameters to the program
             } deriving (Show)
$(mkLabels [''St])

getParams :: TM Params
getParams = TM $ gets params

-- | Write a debug delimiter (a newline)
writeDelimiter :: TM ()
writeDelimiter = write ""

-- | Writes a debug message
write :: String -> TM ()
write = TM . write'

write' :: (MonadState St m) => String -> m ()
write' s = do
  i <- gets debugIndent
  modify debug (dbfolMsg (replicate (i*2) ' ' ++ s):)

warn :: String -> TM ()
warn s = TM $ modify debug (warnMsg s:)

wdproof :: String -> TM ()
wdproof s = TM $ modify debug (dbproofMsg s:)

-- | Do an action with indented debug messages
indented :: TM a -> TM a
indented (TM m) = TM $ do
  modify debugIndent succ
  r <- m
  modify debugIndent pred
  return r

-- | Pop and return the debug messages
popMsgs :: TM [Msg]
popMsgs = TM $ do
  r <- reverse <$> gets debug
  puts debug []
  return r

-- | Perform an action and pop its debug messages and return in a tuple
returnWithDebug :: TM a -> TM (a,[Msg])
returnWithDebug m = liftM2 (,) m popMsgs

-- | Locally manipulate boundNames, and arities since skolem variables
--   are registered as functions with arity 0
locally :: TM a -> TM a
locally (TM m) = TM (locally' m)

locally' :: (MonadState St m) => m a -> m a
locally' m = do
  boundNames' <- gets boundNames
  arities'    <- gets arities
  r <- m
  puts boundNames boundNames'
  puts arities    arities'
  return r

-- | Get the environment for structural induction
getEnv :: Bool -> TM [(Name,[(Name,Type)])]
getEnv addBottom = TM $ do
    untyped <- M.toList <$> gets conFam
    mapM (unTM . addType) untyped
  where
    addType :: (Name,[Name]) -> TM (Name,[(Name,Type)])
    addType (n,cs) = do
        ts <- forM cs $ \c -> fromMaybe
                               (error $ "getEnv unbound con" ++ show c)
                                <$> lookupType c
        let t = head ts
            resTy = case t of
                       TyApp xs -> last xs
                       _        -> t
            bottomList = [ (bottomName,resTy) | addBottom ]

        return (n,zip cs ts ++ bottomList)

-- | Insert /n/ elements to a map of /m/ elements
--
--   /O(n * log(m+n))/
insertMany :: Ord k => [(k,v)] -> Map k v -> Map k v
insertMany kvs m = foldr (uncurry M.insert) m kvs

-- | Looks up the type for a registered function
lookupType :: Name -> TM (Maybe Type)
lookupType n = TM $ M.lookup n <$> gets types

-- | Gets a name from the namesupply
getName :: TM Name
getName = TM $ do
  n <- head <$> gets namesupply
  modify namesupply tail
  return n

bindMeQuantPlease :: Name -> TM VarName
bindMeQuantPlease n = TM $ do
    q@(QuantVar n') <- newQName n
    modify boundNames (M.insert n q)
    return n'

newQName n@(x:xs) = do
    let ok c = isAlphaNum c || c == '_'
    q <- VarName <$>
            if isAlpha x && all ok n
                  then return (toUpper x:xs)
                  else do v <- unTM getName
                          return ("Q_" ++ v)
    return (QuantVar q)

-- | Looks up if a name is a variable or a function/constructor
lookupName :: Name -> TM Bound
lookupName n = TM $ do
    mn <- M.lookup n <$> gets boundNames
    case mn of
      Just b  -> return b
      Nothing -> do -- Variable is unbound, quantify over it
        qv@(QuantVar q) <- newQName n
        write' $ "New quantified variable " ++ show q ++ " for " ++ n
        modify boundNames (M.insert n qv)
        let existsQual = anySuf `isSuffixOf` n
        modify quantified (S.insert (putEither (not existsQual) q))
        return qv

-- | Pop and return the quantified variables
popQuantified :: TM [Either VarName VarName]
popQuantified = TM $ do
  qs <- S.toList <$> gets quantified
  puts quantified S.empty
  return qs

-- | Makes a forall-quantification over all unbound variables in the decl
forallUnbound :: T.Formula -> TM T.Formula
forallUnbound phi = do
  (ex,fa) <- partitionEithers <$> popQuantified
  return $ exists' ex (forall' fa phi)

-- | Makes a new skolem variable for this name
skolemize :: Name -> TM Name
skolemize = skolemFun 0

-- | Makes a new skolem variable for this name with the specified
--   arity when translated to an expression
skolemFun :: Int -> Name -> TM Name
skolemFun arity n = do
  n' <- ((n ++ ".sk") ++) <$> getName
  addFuns [(n',arity)]
  return n'

-- | Add a new indirection
addIndirection :: Name -> Expr -> TM ()
addIndirection n e = TM $ do
    write' $ "indirection: " ++ n ++ " := " ++ prettyCore e
    mem <- M.member n <$> gets boundNames
    when mem $ write' "warn: indirection already exists, overwriting"
    modify boundNames (M.insert n (Indirection e))


-- | fromMaybe with unbound error message from a function
fromUnbound :: String -> Name -> Maybe a -> a
fromUnbound fn n = fromMaybe (error $ fn ++ ", unbound: " ++ n)

-- | Looks up the constructors for a datatype
lookupConstructors :: Name -> TM [Name]
lookupConstructors c = TM $ (fromUnbound "lookupConstructors" c . M.lookup c)
                         <$> gets conFam

-- | Looks up an arity of a function or constructor
lookupArity :: Name -> TM Int
lookupArity n = TM $ (fromUnbound "lookupArity" n . M.lookup n)
                  <$> gets arities

-- | Looks up the projections for a constructor
lookupProj :: Name -> TM [FunName]
lookupProj n = TM $ (fmap FunName . fromUnbound "lookupProj" n . M.lookup n)
                 <$> gets conProj

-- | Make a pointer name of a name
makePtrName :: Name -> Name
makePtrName n = n ++ ".ptr"

-- | Make a pointer of a function name
makeFunPtrName :: FunName -> FunName
makeFunPtrName = FunName . makePtrName . funName

-- | Add functions/constructor name and arity.
addNameAndArity :: MonadState St m =>
                   (FunName -> Bound) -> [(Name,Int)] -> m ()
addNameAndArity mk funs = do
   modify boundNames (insertMany [(n,mk (FunName n))| (n,_) <- funs])
   modify arities (insertMany funs)

addTypes :: [(Name,Type)] -> TM ()
addTypes ts = TM $ do
  mapM_ (\(n,t) -> write' $ "addTypes: " ++ n ++ " :: " ++ show t) ts
  modify types (insertMany ts)

-- | Add functions name and arity
addFuns :: [(Name,Int)] -> TM ()
addFuns = TM . addNameAndArity FunVar

-- | Add a datatype's constructor given the arities
--   Projections are also generated, and added as functions
addCons :: [Decl] -> TM ()
addCons datadecls = TM $ do
    addNameAndArity ConVar (concat css)
    modify conProj (insertMany projs)
    modify datatypes (css ++)
    unTM (addFuns projfuns)
    unTM (mapM_ addTypes (map conTypes datadecls))
    modify conFam (insertMany fams)
  where
    css   = map conNameArity datadecls
    fams  = [ (n,map conName cs) | Data n _ cs <- datadecls ]
    projs = [ projName c | cs <- css, c <- cs]

    projfuns :: [(Name,Int)]
    projfuns = [ (pname,1)
               | cs <- css
               , c <- cs
               , pname <- snd (projName c)
               ]

    projName :: (Name,Int) -> (Name,[Name])
    projName (c,n) = (c,[ N.projName c i | i <- [0..n-1]])

-- | Mark a pointer as used
useFunPtr :: Name -> TM ()
useFunPtr fn = TM $ do
    arity <- unTM $ lookupArity fn
    modify usedFunPtrs (S.insert (fn,arity))

-- | Register a fun ptr
registerFunPtr :: Name -> Int -> TM ()
registerFunPtr fn arity = TM $ do modify usedFunPtrs (S.insert (fn,arity))

getUsedFunPtrs :: TM [(Name,Int)]
getUsedFunPtrs = TM $ S.toList <$> gets usedFunPtrs

-- | A list of nice variable names
varNames :: [String]
varNames = [1..] >>= flip replicateM "XYZWVU"

-- | Make a number of new variable names
makeVarNames :: Int -> [VarName]
makeVarNames n = take n (map VarName varNames)

-- | The name of pointer application
ptrapp :: FunName
ptrapp = FunName "@"

-- | Fold the function app over the arguments
--
-- > appFold f [x,y,z] = app(app(app(f,x),y),z)
-- > appFold f []      = f
appFold :: Term -> [Term] -> Term
appFold = foldl (\f x -> T.Fun ptrapp [f,x])

-- | All FOL declarations from an environment and state
envStDecls :: TM [T.Decl]
envStDecls = TM $ do
  s <- get
  let Params{..} = _params s
  return $ [ extEquality | not thy_no_exteq ] ++
           projDecls (_conProj s) ++
           ptrDecls (_arities s) (_usedFunPtrs s) ++
           disjDecls (_datatypes s)

-- | Make datatypes disjunct.
--
-- > data Maybe = Just a | Nothing
--
-- gives
--
-- > forall x . just x != nothing
-- > forall x . just x != bottom
-- > forall x . nothing != bottom
disjDecls :: [[(Name,Int)]] -> [T.Decl]
disjDecls = concatMap datatypeDisj
  where
    -- Make this datatype's constructors and bottom disjunct
    datatypeDisj :: [(Name,Int)] -> [T.Decl]
    datatypeDisj ctors = concat (zipWith constrDisj ctors'
                                                    (tail (tails ctors')))
      where ctors' = {- (bottomName,0) : -} ctors

    -- Make this constructor unequal to all the constructors in the list
    constrDisj :: (Name,Int) -> [(Name,Int)] -> [T.Decl]
    constrDisj x = map (disjunct x) . filter ((fst x /=) . fst)
                                   -- ^ avoid making bottom/=bottom

    -- Make two constructors disjunct
    disjunct :: (Name,Int) -> (Name,Int) -> T.Decl
    disjunct (c1,a1) (c2,a2) = T.Axiom ("disj" ++ c1 ++ c2)
       $ forall' (xs ++ ys) $ Fun (FunName c1) (map T.Var xs)
                             !=
                             Fun (FunName c2) (map T.Var ys)

      where (xs,ys) = splitAt a1 (makeVarNames (a1 + a2))

-- | Make projection declarations
projDecls :: Map Name [Name] -> [T.Decl]
projDecls = concatMap (uncurry mkDecl) . M.toList
  where
    mkDecl :: Name -> [Name] -> [T.Decl]
    mkDecl c ps = [ Axiom (c ++ "proj" ++ p) $ forall' xs $
                        Fun (FunName p) [Fun (FunName c) (map T.Var xs)]
                        === T.Var x
                  | x <- xs | p <- ps ]
      where arity = length ps
            xs    = makeVarNames arity

-- | Make pointer declarations
ptrDecls :: Map Name Int -> Set (Name,Int) -> [T.Decl]
ptrDecls as = map (uncurry mkDecl) . S.toList
  where
    mkDecl fn arity = Axiom ("ptr" ++ fn)
              $ forall' xs
                $ appFold (Fun (FunName (makePtrName fn)) []) (map T.Var xs)
                  ===
                  Fun (FunName fn) (map T.Var xs)
      where xs    = makeVarNames arity

-- | Extensional equality
extEquality :: T.Decl
extEquality = Axiom "exteq"
   $ forall' [fv,gv]
      $ (forall' [xv] $ appFold f [x] === appFold g [x])
        ==> (f === g)
  where vars@[fv,gv,xv] = map VarName ["F","G","X"]
        [f,g,x]         = map T.Var vars

-- | Application with bottom gives bottom
appBottom :: T.Decl
appBottom = Axiom "appbottom"
   $ forall' [xv] $ appFold bottom [x] === bottom
  where xv = VarName "X"
        x  = T.Var xv
        bottom = Fun (FunName bottomName) []
