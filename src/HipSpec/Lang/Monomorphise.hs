-- | Monomorphises the Simple language, given some initial activated
--   records. The idea is that these activation records come from
--   a monomorphised conjecture.
module HipSpec.Lang.Monomorphise where

import HipSpec.Lang.Type
import HipSpec.Lang.Simple
import qualified Data.Set as S
import Data.Set (Set)

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Applicative

-- type Prog a = ([Datatype a],[Function a])

-- | an activation record
type Record a = (a,[Type a])

type Subst a = [(a,Type a)]

-- | Can make a new identifier of a substitution
type Inst a
    =  [(a,Type a)] {- ^ substitution, from the top level function/ty con -}
    -> [Type a] {- ^ applied variables, to this particula identifier -}
    -> a {- ^ identifier -}
    -> a {- ^ result -}

-- monoProg :: Ord a => [Datatype a] -> [Function a] -> [(a,[Type a])]

-- | Instantiate a function to some types, giving the new function and new
--   activated records. The instantiated type should (obviously) be
--   monomorphic. Care needs to be taken so the records don't contain the
--   free variables of functions (from arguments and case)
instFunc :: Ord a => Inst a -> Function a -> [Type a] -> (Function a,Set (Record a))
-- monomorphic functions needn't be instantiated
instFunc _  fn@(Function _ [] _ _) _ = (fn,S.empty)
-- the interesting case
instFunc iv (Function f tvs as b) ts = flip runReader (iv,su) $ runWriterT $ do
    f' <- instId f ts
    as' <- mapM (`instId` []) as
    b' <- ignoreLocal as' $ instBody b
    return $ Function f' [] as' b'
  where
    su = zip tvs ts

-- | The instantiation monad: has a current substitution, carries around
--   the instantiation function and keeps a set of activated records
type InstM a = WriterT (Set (Record a)) (Reader (Inst a,Subst a))

instId :: Ord a => a -> [Type a] -> InstM a a
instId x ts = do
    (iv,su) <- ask
    return (iv su ts x)

recordId :: Ord a => a -> [Type a] -> InstM a ()
recordId = curry (tell . S.singleton)

instrecId :: Ord a => a -> [Type a] -> InstM a a
instrecId x ts = do
    x' <- instId x ts
    recordId x ts
    return x'

ignoreLocal :: Ord a => [a] -> InstM a b -> InstM a b
ignoreLocal lcs = censor (S.\\ S.fromList (lcs `zip` repeat []))

instBody :: Ord a => Body a -> InstM a (Body a)
instBody b = case b of
    Case e alts -> Case <$> instExpr e <*> mapM instAlt alts
    Body e      -> Body <$> instExpr e

instAlt :: Ord a => Alt a -> InstM a (Alt a)
instAlt (p,b) = case p of
    ConPat c ts as -> do
        c' <- instrecId c ts
        as' <- mapM (`instId` []) as
        b' <- ignoreLocal as' (instBody b)
        return (ConPat c' [] as',b')
    Default    -> (,) Default <$> instBody b
    LitPat i a -> (,) (LitPat i a) <$> instBody b

instExpr :: Ord a => Expr a -> InstM a (Expr a)
instExpr e = case e of
    Var x ts  -> Var <$> instrecId x ts <*> pure []
    App e1 e2 -> App <$> instExpr e1 <*> instExpr e2
    Lit{}     -> return e

_test_map :: Function String
_test_map = Function "map" ["a","b"] ["f","xs"] $ Case (Var "xs" [])
    [ (ConPat "cons" [TyVar "a"] ["y","ys"],Body $ Var "cons" [TyVar "b"] `App` (Var "f" [] `App` Var "x" []) `App` (Var "map" [TyVar "a",TyVar "b"] `App` Var "f" [] `App` Var "ys" []))
    , (ConPat "nil" [TyVar "a"] [],Body $ Var "nil" [TyVar "b"])
    ]

_test_inst :: [(String,Type String)] -> [Type String] -> String -> String
_test_inst _ [] x = x
_test_inst _ ts x = x ++ show ts

_test = instFunc _test_inst _test_map [TyVar "A",TyVar "B"]

