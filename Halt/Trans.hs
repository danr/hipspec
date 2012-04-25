-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, PatternGuards,
             RecordWildCards, NamedFieldPuns,
             GeneralizedNewtypeDeriving,
             FlexibleContexts
  #-}
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
import Data.List (delete,intercalate)

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


-- Pushes new quantified variables to the environment
pushQuant :: [Var] -> HaltEnv -> HaltEnv
pushQuant qs env = env { quant = qs ++ quant env }

-- Deletes a variable from the quantified list
delQuant :: Var -> HaltEnv -> HaltEnv
delQuant v env = env { quant = delete v (quant env) }


-- Pushes a new constraint to an environment
pushConstraint :: Constraint -> HaltEnv -> HaltEnv
pushConstraint c = pushConstraints [c]

-- Pushes many new constraints to an environment
pushConstraints :: [Constraint] -> HaltEnv -> HaltEnv
pushConstraints cs env = env { constr = cs ++ constr env }

-- Sets the current substitutions
extendSubs :: Subs -> HaltEnv -> HaltEnv
extendSubs s env = env { subs = s `M.union` subs env }

-- Extends the arities
extendArities :: ArityMap -> HaltEnv -> HaltEnv
extendArities am env = env { arities = am `M.union` arities env }

-- Substitiotions: maps variables to expressions
type Subs = Map Var CoreExpr

-- Constraints from case expressions to results, under a substitution
data Constraint = CoreExpr :== Pattern
                | CoreExpr :/= Pattern

-- A pattern
data Pattern = Pattern DataCon [CoreExpr]

trPattern :: Pattern -> CoreExpr
trPattern (Pattern data_con as) = foldl App (Var (dataConWorkId data_con)) as

instance Show Pattern where
  show = showExpr . trPattern

instance Show Constraint where
  show (e :== p) = showExpr e ++ " :== " ++ show p
  show (e :/= p) = showExpr e ++ " :/= " ++ show p

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
            , args    = []
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
      arities = M.fromList [(v,arity e) | (v,e) <- binds ]

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

-- trBind :: CoreBind -> Halt [Formula]
-- trBind bind =
--   let defns :: [(Var,[Var],CoreExpr)]
--       defns = [ (v,as,e')
--               | (v,e) <- flattenBinds [bind]
--               , let (_ty,as,e') = collectTyAndValBinders e
--               ]
--
--       arities :: ArityMap
--       arities = [ (v,length as) | (v,as,e') <- defns ]

-- | Write a debug message
write :: MonadWriter [String] m => String -> m ()
write = tell . return

-- | Translate a CoreDecl or a Let
trDecl :: Var -> CoreExpr -> HaltM [Formula]
trDecl f e = do
    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
    local (\env -> env { fun = f
                       , args = as ++ args env
                       , quant = as ++ quant env}) (trCase e')
  where -- Collect the arguments and the body expression
    as :: [Var]
    e' :: CoreExpr
    (_ty,as,e') = collectTyAndValBinders e
    -- Dangerous? Type variables are skipped for now.

-- | The arity of an expression if it is a lambda
arity :: CoreExpr -> Int
arity e = length as
  where (_,as,_) = collectTyAndValBinders e

-- | Translate a case expression
trCase :: CoreExpr -> HaltM [Formula]
trCase e = case e of
    Case{} -> do
        -- Add a bottom case
        let Case scrutinee scrut_var _ty ((DEFAULT,[],def_expr):alts) = addBottomCase e

        write $ "Case on " ++ showExpr scrutinee

        -- Translate the scrutinee and add it to the substitutions
        local (extendSubs (M.singleton scrut_var scrutinee)) $ do

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
        HaltEnv{fun,args,quant,constr} <- ask
        write $ "At the end of " ++ idToStr fun ++ "'s branch: " ++ showExpr e
        write $ "Constraints: " ++ concatMap ("\n    " ++) (map show constr)
        if conflict constr
            then write "  Conflict!" >> return []
            else do
                (form,extra_formulae) <- runWriterT $ do
                    lhs <- mkFun fun <$> mapM (trExpr . Var) args
                    rhs <- trExpr e
                    tr_constr <- translateConstr constr
                    return $ forall' (map mkVarName quant)
                                     (tr_constr =:=> (lhs === rhs))
                return (form : extra_formulae)

type ExprHaltM a = WriterT [Formula] HaltM a

(=:=>) :: [Formula] -> Formula -> Formula
[] =:=> phi = phi
xs =:=> phi = phi \/ foldr1 (\/) (map neg xs)

conflict :: [Constraint] -> Bool
conflict cs = or [ cheapExprEq e1 e2 && con_x == con_y
                 | e1 :== Pattern con_x _ <- cs
                 , e2 :/= Pattern con_y _ <- cs
                 ]

cheapExprEq (Var x) (Var y) = x == y
cheapExprEq (App e1 e2) (App e1' e2') = cheapExprEq e1 e2 && cheapExprEq e1' e2'
cheapExprEq _ _ = False

translateConstr :: [Constraint] -> ExprHaltM [Formula]
translateConstr cs = sequence $ [ trConstr (===) e p | e :== p <- cs ] ++
                                [ trConstr (!=) e p  | e :/= p <- cs ]
  where
    trConstr :: (Term -> Term -> Formula)
             -> CoreExpr -> Pattern -> ExprHaltM Formula
    trConstr (~~) e (Pattern data_con as) = do
        lhs <- trExpr e
        rhs <- mkFun (dataConWorkId data_con) <$> mapM trExpr as
        return $ lhs ~~ rhs

invertAlt :: CoreExpr -> CoreAlt -> Constraint
invertAlt scrut_exp (con, bs, _) = case con of
  DataAlt data_con -> constraint
    where
      con_name   = dataConName data_con
      proj_binds = [ projExpr con_name i scrut_exp | b <- bs | i <- [0..] ]
      constraint = scrut_exp :/= Pattern data_con proj_binds

  DEFAULT -> error "invertAlt on DEFAULT"
  _       -> error "invertAlt on LitAlt (literals not supported yet!)"


trAlt :: CoreExpr -> CoreAlt -> HaltM Formulae
trAlt scrut_exp (con, bound, e) = do
  env@HaltEnv{quant} <- ask
  case con of

    DataAlt data_con -> local upd_env (trCase e)
      where
        pat = Pattern data_con (map Var bound)
        upd_env = case scrut_exp of
            Var x
              | x `elem` quant -> extendSubs (M.singleton x (trPattern pat))
                                . pushQuant bound
                                . delQuant x
            _ -> pushConstraint (scrut_exp :== pat)
               . pushQuant bound

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


getLabel :: (MonadState Int m) => m Int
getLabel = do { x <- get ; modify succ ; return x }

foldFunApps :: Term -> [Term] -> Term
foldFunApps = foldl (\x y -> Fun (FunName "app") [x,y])

-- | Translate an expression, i.e. not case statements. Substitutions
-- are followed.
trExpr :: CoreExpr -> ExprHaltM Term
trExpr e = do
    env@HaltEnv{..} <- ask
    case e of
        Var x | Just e' <- M.lookup x subs -> do lift $ write $ "Following subst " ++ showExpr e ++ " to " ++ showExpr e'
                                                 trExpr e'
              | x `elem` quant             -> return (mkVar x)
              | otherwise                  -> return (mkFun x [])
        App{} -> do
          lift $ write $ "App on " ++ showExpr e
          case second trimTyArgs (collectArgs e) of
            -- We should first try to translate App, since they might
            -- contain substitutions.
            -- TODO : Use the arities and add appropriate use of app
            (Var x,es)
               | Just e' <- M.lookup x subs -> error "application of something in subs"
               | Just i <- M.lookup x arities -> do
                   lift $ write $ idToStr x ++ " found in arity map with arity " ++ show i
                   if i > length es
                       then foldFunApps (mkPtr x) <$> mapM trExpr es
                       else do
                           let (es_inner,es_after) = splitAt i es
                           inner <- mkFun x <$> mapM trExpr es_inner
                           foldFunApps inner <$> mapM trExpr es_after
               -- | x `M.notMember` subs -> mkFun x <$> mapM trExpr es
            (f,es) -> do
               lift $ write $ "Collected to " ++ showExpr f ++ " on " ++ intercalate "," (map showExpr es)
               foldFunApps <$> trExpr f <*> mapM trExpr es
        Lit (MachStr s) -> do
          lift $ write $ "String to constant: " ++ unpackFS s
          return $ Fun (FunName "string") [Fun (FunName (unpackFS s)) []]

        Case{}      -> trCaseExpr e
        Let bind e' -> trLet bind e'
        Cast e' _   -> do
          lift $ write $ "Ignoring cast: " ++ showExpr e
          trExpr e'

        Lit{}      -> trErr e "literals"
        Type{}     -> trErr e "types"
        Lam{}      -> trErr e "lambdas"
        Coercion{} -> trErr e "coercions"
        Tick{}     -> trErr e "ticks"
  where trErr e s = error ("trExpr: no support for " ++ s ++ "\n" ++ showExpr e)

-- | Translate a local case expression
trCaseExpr :: CoreExpr -> ExprHaltM Term
trCaseExpr e = do
    lift $ write $ "Experimental case: " --  ++ showExpr e
    new_fun <- modVar "case" =<< asks fun
    quant_vars <- asks quant
    tell =<< lift (local (\env -> env { fun = new_fun , args = quant_vars}) (trCase e))
    mkFun new_fun <$> mapM (trExpr . Var) quant_vars

-- | Translate a let expression
--   TODO: This copies some functionality found elsewhere
trLet :: CoreBind -> CoreExpr -> ExprHaltM Term
trLet bind in_e = do
    lift $ write $ "Experimental let: " -- ++ showExpr (Let bind in_e)
    binds <- sequence [ do { v' <- modVar "" v ; return (v,v',e) }
                       | (v,e) <- flattenBinds [bind] ]
    env@HaltEnv{..} <- ask
    let new_subs = M.fromList [ (v,foldl App (Var v') (map Var quant))
                              | (v,v',_) <- binds ]
        -- ^ These needs to be subs because constraints have already been
        --   finalized and turned into subs for in_e.

    let arities :: ArityMap
        arities = M.fromList [(v',arity e + length quant) | (v,v',e) <- binds ]

    local (extendArities arities . extendSubs new_subs) $ do
      mapM (\(_,v',e) -> tell =<< lift (trDecl v' e)) binds
      trExpr in_e

modVar :: MonadState Int m => String -> Var -> m Var
modVar lbl v = do
    i <- getLabel
    let var_name = mkInternalName (mkPreludeMiscIdUnique i)
                                  (mkOccName dataName $ lbl ++ show i ++ idToStr v)
                                  wiredInSrcSpan
    return $ mkVanillaGlobal var_name (error $ "modVar, " ++ lbl ++ ": type")

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

mkPtr :: Var -> Term
mkPtr = (`Fun` []) . FunName . (++ "ptr") . map toLower . idToStr

mkFun :: Var -> [Term] -> Term
mkFun = Fun . FunName . map toLower . idToStr

mkVarName :: Var -> VarName
mkVarName = VarName . (\(x:xs) -> toUpper x : xs) . idToStr

mkVar :: Var -> Term
mkVar = FVar . mkVarName

