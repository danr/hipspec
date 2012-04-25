-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, PatternGuards,
             RecordWildCards, NamedFieldPuns,
             GeneralizedNewtypeDeriving #-}
module Halt.Trans where

import PprCore

import MkCore
import CoreSyn
import CoreUtils
import Var
import DataCon
import Id
import Name
import Outputable
import Literal
import FastString

import Unique
import SrcLoc

import Halt.Names
import Halt.Util
import FOL.Syn hiding ((:==))

import qualified Data.Map as M
import Data.Map (Map)
import Data.Char (toUpper,toLower)
import Data.List (delete)

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative


-- Nice functions from CoreSyn.lhs

-- flattenBinds :: [Bind b] -> [(b,Expr b)]
-- Probably want to flatten everything out, we don't really care that
-- we can get it nicely in SCCs. Futhermore a quick pass over this
-- let's us see how many arguments each function takes.

-- collectBinders :: Expr b -> ([b],Expr b)
-- takes a \x y z -> e and return ([x,y,z],e), but we might also need to
-- take type variables too. for now, let us assure no polymorphism so
-- there are no type variables

-- collectArgs :: Expr b -> (Expr b, [Arg b])
-- takes a nested app and returns the expression to be applied to it

-- Map associating each function/CAF with its arity
type ArityMap = Map Var Int

-- The Environment
data HaltEnv
  = HaltEnv { arities  :: ArityMap
            -- ^ Arities of top level definitions
            , fun      :: Var
            -- ^ Current function
            , args     :: [Var]
            -- ^ Arguments to current function
            , quant    :: [Var]
            -- ^ Quantified variables
            , constr   :: [Constraint]
            -- ^ Constraints
            , subs     :: Subs
            -- ^ Substitutions
            }

-- Pushes a new constraint to an environment
pushConstraint :: Constraint -> HaltEnv -> HaltEnv
pushConstraint c env = env { constr = c : constr env }

-- Sets the current substitutions
extendSubs :: Subs -> HaltEnv -> HaltEnv
extendSubs s env = env { subs = s `M.union` subs env }

-- Substitiotions: maps variables to expressions
type Subs = Map Var CoreExpr

-- Constraints from case expressions to results, under a substitution
data Constraint = Var      :-> CoreExpr
                | CoreExpr :== CoreExpr
                | CoreExpr :/= CoreExpr

-- | The empty substitution
noSubs :: Subs
noSubs = M.empty

-- | The empty constraints
noConstraints :: [Constraint]
noConstraints = []

-- | The initial environment
initEnv :: ArityMap -> HaltEnv
initEnv am
  = HaltEnv { arities = am
            , fun     = error "initEnv: fun"
            , args    = error "initEnv: args"
            , quant   = []
            , constr  = noConstraints
            , subs    = M.empty
            }

-- | The translation monad
newtype HaltM a
  = HaltM { runHaltM :: ReaderT HaltEnv (WriterT [String] (State Int)) a }
  deriving (Applicative,Monad,Functor
           ,MonadReader HaltEnv
           ,MonadWriter [String]
           ,MonadState Int)

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
--   TODO: Register used function pointers
--   TODO: Assumes only nested case expression at top level of the body
--         of a function. Possible fix: top level lift all other case expressions
translate :: [CoreBind] -> ([FDecl],[String])
translate program =
  let -- Let-lift the program
      liftedProgram :: [CoreBind]
      liftedProgram = program

      -- Remove the unnecessary SCC information
      binds :: [(Var,CoreExpr)]
      binds = flattenBinds liftedProgram

      -- Arity of each function (Arities from other modules are also needed)
      arities :: ArityMap
      arities = M.fromList [(v,length (fst (collectBinders e))) | (v,e) <- binds ]

      -- Translate each declaration
      -- TODO : Make these return Decl?
      translated :: HaltM [Formula]
      translated = concatMapM (uncurry trDecl) binds

      formulae :: [Formula]
      msgs :: [String]
      (formulae,msgs) = runWriterT
                            (runHaltM translated `runReaderT` initEnv arities)
                            `evalState` 0

  in  ([ FDecl Axiom ("decl" ++ show n) phi
       | phi <- formulae
       | n <- [(0 :: Int)..] ]
      ,msgs)

write :: String -> HaltM ()
write = tell . return

-- Substitutions from variables bound in cases
-- | Translate a CoreDecl
trDecl :: Var -> CoreExpr -> HaltM [Formula]
trDecl f e = do
    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
    local (\e -> e { fun = f , args = as , quant = as }) (trCase e')
  where -- Collect the arguments and the body expression
    as :: [Var]
    e' :: CoreExpr
    (_ty,as,e') = collectTyAndValBinders e

trCase :: CoreExpr -> HaltM [Formula]
trCase e = case e of
  Case{} -> do
    -- Add a bottom case
    let Case scrutinee scrut_var _ty ((DEFAULT,[],def_expr):alts) = addBottomCase e

    write $ "Case on " ++ showExpr scrutinee

    -- Translate the scrutinee and add it to the substitutions
    local (pushConstraint (scrut_var :-> scrutinee)) $ do

        -- Translate the alternatives (mutually recursive with this
        -- function)
        alt_formulae <- concatMapM (trAlt scrutinee) alts

        -- Collect the negative patterns
        let neg_constrs = map (invertAlt scrutinee) alts

        -- Translate the default formula which happens on the negative
        -- constraints
        def_formula <- local (\env -> env { constr = neg_constrs ++ constr env })
                             (trCase def_expr)

        return (def_formula ++ alt_formulae)
  _ -> do
    -- When translating expressions, only subs are considered, not
    -- constraints.  The substitutions come from constraints of only a
    -- variable, which in turn come from unifying the scrut var with
    -- the scrutinee and casing on variables.
    (subs',pos,neg) <- collectConstr <$> asks constr
    local (extendSubs subs') $ do
      HaltEnv{fun,args,quant} <- ask
      write $ "At the end of a branch: " ++ showExpr e
      (form,extra_formulae) <- runWriterT $ do
        lhs <- mkFun fun <$> mapM (trExpr . Var) args
        rhs <- trExpr e
        tr_pos <- mapM (\(a,b) -> liftM2 (===) (trExpr a) (trExpr b)) pos
        tr_neg <- mapM (\(a,b) -> liftM2 (!=)  (trExpr a) (trExpr b)) neg
        return $ forall' (map mkVarName quant) ((tr_pos ++ tr_neg) =:=> (lhs === rhs))
      return (form : extra_formulae)

(=:=>) :: [Formula] -> Formula -> Formula
[] =:=> phi = phi
xs =:=> phi = foldr1 (/\) xs ==> phi

type Eqp = (CoreExpr,CoreExpr)

collectConstr :: [Constraint] -> (Map Var CoreExpr,[Eqp],[Eqp])
collectConstr cs = (M.fromList [ (x,e)     | x :-> e <- cs ]
                   ,           [ (lhs,rhs) | lhs :== rhs <- cs ]
                   ,           [ (lhs,rhs) | lhs :/= rhs <- cs ])


invertAlt :: CoreExpr -> CoreAlt -> Constraint
invertAlt scrut_exp (con, bs, _) = case con of
  DataAlt data_con -> constraint
    where
      con_name   = dataConName data_con
      proj_binds = [ projExpr con_name i scrut_exp | b <- bs | i <- [0..] ]
      rhs        = foldl App (Var (dataConWorkId data_con)) proj_binds
      constraint = scrut_exp :/= rhs
      -- This is Dangerous. rhs is a CoreExpr but invalid; does not apply
      -- type arguments properly. This can be seen if mkCoreConApps is used
      -- instead: the impossible happens.

  DEFAULT -> error "invertAlt on DEFAULT"
  _       -> error "invertAlt on LitAlt (literals not supported yet!)"


trAlt :: CoreExpr -> CoreAlt -> HaltM Formulae
trAlt scrut_exp (con, bound, e) = do
  env@HaltEnv{quant} <- ask
  case con of

    DataAlt data_con -> local (const new_env) (trCase e)
      where
        rhs = foldl App (Var (dataConWorkId data_con)) (map Var bound)
        -- ^ See comment about Dangerous in invertAlt
        (new_constraint,new_quant) = case scrut_exp of
            Var x | x `elem` quant -> (x :-> rhs,bound ++ delete x quant)
            _                      -> (scrut_exp :== rhs,bound ++ quant)
        new_env = pushConstraint new_constraint env { quant = new_quant }

    DEFAULT -> error "trAlt on DEFAULT"
    _       -> error "trAlt on LitAlt (literals not supported yet!)"


{-

  Note about the DEFAULT case and bottom. Two situations:

  1) There is a DEFAULT case. Add a bottom alternative:

      case e of                  case e of
        DEFAULT -> e0              DEFAULT -> e0
        K1 a    -> e1      =>      K1 a    -> e1
        K2 a b  -> e2              K2 a b  -> e2
                                   Bottom  -> Bottom

  2) No DEFAULT case. Add such a case to Bottom.

      case e of                  case e of
        K1 a    -> e1              DEFAULT -> Bottom
        K2 a b  -> e2      =>      K1 a    -> e1
                                   K2 a b  -> e2

-}
-- | Adds a bottom case as described above.
--   The input must be a case expression!
addBottomCase :: CoreExpr -> CoreExpr
addBottomCase (Case scrutinee binder ty alts) =
  let -- _|_ -> _|_
      -- Breaks the core structure by having a new data constructor
      bottomAlt :: CoreAlt
      bottomAlt = (DataAlt bottomCon, [], bottomVar)

      -- DEFAULT -> _|_
      defaultBottomAlt :: CoreAlt
      defaultBottomAlt = (DEFAULT, [], bottomVar)
  -- Case expressions have an invariant that the default case is always first.
  in Case scrutinee binder ty $ case findDefault alts of
       (as,Just def) -> (DEFAULT, [], def):bottomAlt:as
       (as,Nothing)  -> defaultBottomAlt:as
addBottomCase _ = error "addBottomCase on non-case expression"

-- | Translate an expression, i.e. not case statements. Substitutions
-- are followed.
trExpr :: CoreExpr -> WriterT [Formula] HaltM Term
trExpr e = do
  env@HaltEnv{..} <- ask
  case e of
    Var x | Just e' <- M.lookup x subs -> trExpr e'
          | x `elem` quant             -> return (mkVar x)
          | otherwise                  -> return (mkFun x [])
    App{} -> case second trimTyArgs (collectArgs e) of
                    -- TODO : Use the arities and add appropriate use of app
                    (Var x,es) -> mkFun x <$> mapM trExpr es
                    (f,es)     -> foldl (\x y -> Fun (FunName "ptrApp") [x,y])
                                     <$> trExpr f
                                     <*> mapM trExpr es
    Lit (MachStr s) -> return (Fun (FunName "string") [Fun (FunName (unpackFS s)) []])
    Lit{}      -> trErr e "literals"
    Cast e _   -> trExpr e -- trErr e "casts"
    Type{}     -> trErr e "types"
    Lam{}      -> trErr e "lambdas"
    Let{}      -> trErr e "let stmnts"
--    Note{}     -> trErr e "notes"
    Coercion{} -> trErr e "coercions"
    Tick{}     -> trErr e "ticks"
    Case{}     -> do
      i <- lift $ do { x <- get ; modify succ ; return x }
      lift $ write $ "Experimental case:  " ++ showExpr e
      let cfunName = mkInternalName (mkPreludeMiscIdUnique 0)
                                    (mkOccName dataName $ "case" ++ show i)
                                    wiredInSrcSpan
          cfunVar = mkVanillaGlobal cfunName (error "cfunVar: type")
      tell =<< lift (local (\env -> env { fun = cfunVar , args = quant }) (trCase e))
      mkFun cfunVar <$> mapM (trExpr . Var) quant
  where trErr e s = error ("trExpr: no support for " ++ s ++ "\n" ++ showExpr e)

showExpr :: CoreExpr -> String
showExpr = showSDoc . pprCoreExpr

trimTyArgs :: [CoreArg] -> [CoreArg]
trimTyArgs = filter (not . isTyArg)
  where
    isTyArg Type{} = True
    isTyArg _      = False


idToStr :: Id -> String
idToStr = showSDocOneLine . ppr . maybeLocaliseName . idName
  where
    maybeLocaliseName n | isSystemName n = n
                        | otherwise      = localiseName n

mkFun :: Var -> [Term] -> Term
mkFun = Fun . FunName . map toLower . idToStr

mkVarName :: Var -> VarName
mkVarName = VarName . (\(x:xs) -> toUpper x : xs) . idToStr

mkVar :: Var -> Term
mkVar = FVar . mkVarName

