{-# LANGUAGE FlexibleContexts #-}
module Hip.Test.GenerateTests where

import Hip.Trans.Core -- use Data Decls and Types from there
import Hip.Trans.Pretty

import Control.Monad.Random
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Applicative

import System.Process

import Data.Maybe
import Data.List


--type GM = RandT StdGen (State [Decl])
type GM = Rand StdGen

-- | Gets a random element from a list
getRandomElem :: RandomGen g => [a] -> Rand g a
getRandomElem xs = (xs !!) <$> getRandomR (0,length xs - 1)

-- | Makes an integer nicely representable as a string
intToStr :: Int -> String
intToStr i = (flip replicateM ['a'..'z'] =<< [1..]) !! i

lrange :: Int -> [Int]
lrange i = [0..i-1]

-- | Makes a random type
makeType :: [Name]
         -- ^ Available type constructors
         -> GM Type
makeType ns = (`TyCon` []) <$> getRandomElem ns

-- | Makes a monomorphic data type
makeDataType :: [Name]
             -- ^ Data types available
             -> Name
             -- ^ Name of the data type
             -> GM Decl
makeDataType datas name = do
    num_cons <- getRandomR (1,2)
    cons <- forM (lrange num_cons) $ \i -> do
                num_args <- getRandomR (1,3)
                args <- replicateM num_args $ do rand_con <- (0 ==) <$> getRandomR (0 :: Int,3)
                                                 if rand_con then makeType datas
                                                             else makeType [name]
                return $ Cons (name ++ "C" ++ intToStr i) args
    let def_cons = Cons (makeBaseCon name) []
    return $ Data name [] (def_cons : cons)

-- | Makes the base constructor for a data type
makeBaseCon :: Name -> Name
makeBaseCon = (++ "B")

-- | Makes some monomorphic data types
makeDataTypes :: Int -> GM [Decl]
makeDataTypes num_datas = do
    let data_names = map (\i -> 'D' : intToStr i) (lrange num_datas)
    mapM (makeDataType data_names) data_names

-- | Gets a random constructor from a datatype
getRandomCons :: Name -> [Decl] -> GM Cons
getRandomCons name = getRandomElem
                   . dataCons
                   . fromMaybe (error "getRandomCons")
                   . find ((name ==) . declName)

data Fun = Fun { funName   :: Name
               , funMatrix :: [([Pattern],Expr)]
               , funType   :: Type
               }
  deriving (Eq,Ord)

type TypedNames = [(Type,Name)]

type SupplyTypedNamesM = WriterT TypedNames (StateT Int GM)

write :: (Monad m,MonadWriter [a] m) => a -> m ()
write = tell . return

newName :: (Monad m,MonadState Int m) => m Name
newName = do x <- get
             modify succ
             return $ "x" ++ show x

-- | Makes a random function in an environment of data types
makeFun :: [Decl] -> Name -> GM Fun
makeFun datas fun_name = do
    let data_names = map declName datas
    num_args <- getRandomR (1,3)
    args_ty  <- replicateM num_args (makeType data_names)
    res_ty   <- getRandomElem args_ty
    num_cl   <- getRandomR (2,6)
    clauses  <- replicateM num_cl (makeClause args_ty res_ty)
    -- Remove def_clause if you want to test bottoms
    let def_clause = ([ PVar (intToStr n) | (_,n) <- zip args_ty [0..]]
                     ,baseExpr res_ty)
    return (Fun fun_name (clauses ++ [def_clause])
                (TyApp (args_ty ++ [TyCon "List" [res_ty]])))
  where
    baseExpr :: Type -> Expr
    baseExpr res_ty = Con "Cons" [Con (makeBaseCon (unTyCon res_ty)) []
                                 ,Con "Nil" []]

    makeClause :: [Type] -> Type -> GM ([Pattern],Expr)
    makeClause args_ty res_ty = do
        (ps,typed_names) <- (`evalStateT` 0)
                          . runWriterT
                          . forM args_ty $ \ty -> do d <- getRandomR (1,3)
                                                     makePat False datas ty d
        rec <- makeRecCall args_ty res_ty typed_names
        case rec of Just e  -> return (ps,e)
                    Nothing -> return (ps,baseExpr res_ty)

    makeRecCall :: [Type] -> Type -> TypedNames -> GM (Maybe Expr)
    makeRecCall args_ty res_ty typed_names = do
        attempt <- forM args_ty $ \ty -> case filter ((ty ==) . fst) typed_names of
                                             [] -> return Nothing
                                             ns -> Just . snd <$> getRandomElem ns
        value <- fromMaybe (Con (makeBaseCon (unTyCon res_ty)) []) <$> case filter ((res_ty ==) . fst) typed_names of
                                                                            [] -> return Nothing
                                                                            ns -> Just . Var . snd <$> getRandomElem ns
        return $ if any isNothing attempt
                     then Nothing
                     else Just (Con "Cons" [value,App fun_name (map (Var . fromJust) attempt)])

unTyCon :: Type -> Name
unTyCon (TyCon data_type []) = data_type
unTyCon _                    = error "unTyCon"

-- | Makes a random pattern of a given type up to a certain depth
makePat :: Bool -> [Decl] -> Type -> Int -> SupplyTypedNamesM Pattern
makePat closed datas ty 0 | closed    = return (PCon (makeBaseCon (unTyCon ty)) [])
                          | otherwise = do n <- newName
                                           write (ty,n)
                                           return (PVar n)
makePat closed datas ty d = do
    force_var <- return False -- (0  ==) <$> getRandomR (0,d)
    if force_var
       then makePat closed datas ty d
       else do let data_type = unTyCon ty
               Cons con_name con_args <- (lift . lift) (getRandomCons data_type datas)
               ps <- mapM (\t -> makePat closed datas t (d-1)) con_args
               return (PCon con_name ps)

-- | Makes a random value of a given type up to a certain depth
makeValue :: [Decl] -> Type -> Int -> SupplyTypedNamesM Expr
makeValue datas ty d = patternToExpr <$> makePat True datas ty d

makeFuns :: [Decl] -> Int -> GM [Fun]
makeFuns datas num_funs = do
    let fun_names = map (\x -> 'f' : show x) (lrange num_funs)
    mapM (makeFun datas) fun_names

makeFunApp :: [Decl] -> [Fun] -> GM (Expr,Type)
makeFunApp datas funs = do
   (Fun fun_name _ fun_ty) <- getRandomElem funs
   let args_ty = argsTypes fun_ty
   (args,_) <- (`evalStateT` 0)
             . runWriterT
             . forM args_ty $ \ty -> do d <- getRandomR (2,4)
                                        makeValue datas ty d
   return (App fun_name args,resType fun_ty)

ppFun :: Fun -> String
ppFun (Fun name matrix fun_ty) = unlines ((name ++ " :: " ++ show fun_ty)
                                         : map ppRow matrix)
  where
    ppRow (ps,e) = name ++ " " ++ intercalate " " (map (\p -> "(" ++ show p ++ ")") ps)
                   ++ " = " ++ show e

main :: IO ()
main = do
    let list = Data "List" ["a"] [Cons "Cons" [TyVar "a",TyCon "List" [TyVar "a"]]
                                 ,Cons "Nil"  []]
    datas <- evalRandIO $ makeDataTypes 1
    funs  <- evalRandIO $ makeFuns datas 5
    (apps,appstype) <- unzip <$> (evalRandIO $ replicateM 500 (makeFunApp datas funs))
    let source = unlines (map ((++ "deriving (Show)") . reverse . drop 1 . reverse . show) (list : datas) ++
                          map ppFun funs)
              ++ "main = do\n\t" ++ intercalate "\n\t" (map (\e -> "print (" ++ show e ++ ")") apps)
    --putStrLn source
    values <- lines <$> readProcess "runghc" ["-w"] source
    let props = unlines $ zipWith4 (\e ty v n -> "prop_" ++ show n ++ " :: " ++ "Prop (" ++ show ty ++ ")\n" ++
                                                 "prop_" ++ show n ++ " = " ++ v ++ " =:= " ++ show e)
                               apps appstype values [(0 :: Int)..]
    let consistency = "inconsistent :: Prop Bool\ninconsistent = True =:= False\n"
    putStrLn (source ++ props ++ consistency)


