-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, PatternGuards, RecordWildCards, GeneralizedNewtypeDeriving #-}
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

import Halt.Names
import Halt.Util
import FOL.Syn

import qualified Data.Map as M
import Data.Map (Map)
import Data.Char (toUpper,toLower)

import Control.Monad.Reader
import Control.Monad.Writer
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

-- Substitiotions: maps variables to expressions
type Subs = Map Var CoreExpr

-- Constraints from case expressions to results, under a substitution
data Constraint = Subst Var      CoreExpr [Var] -- substVar, substRhs, substBound
                | Equal CoreExpr CoreExpr [Var] -- equalLhs, equalRhs, equalBound
                | CoreExpr :=/= CoreExpr

-- | The empty substitution
noSubs :: Subs
noSubs = M.empty

-- | The empty constraints
noConstraints :: [Constraint]
noConstraints = []

initEnv :: ArityMap -> HaltEnv
initEnv am = HaltEnv { arities = am
                     , fun     = error "initEnv: fun"
                     , args    = error "initEnv: args"
                     , quant   = []
                     , constr  = noConstraints
                     , subs    = noSubs
                     }

-- | The translation monad
newtype HaltM a = HaltM { runHaltM :: Reader HaltEnv a }
  deriving (Applicative,Monad,Functor,MonadReader HaltEnv)

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
--   TODO: Register used function pointers
--   TODO: Assumes only nested case expression at top level of the body
--         of a function. Possible fix: top level lift all other case expressions
translate :: [CoreBind] -> [FDecl]
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
      translated= concatMapM (uncurry trDecl) binds

  in  [ FDecl Axiom ("decl" ++ show n) phi
      | phi <- runHaltM translated `runReader` (initEnv arities)
      | n <- [(0 :: Int)..]
      ]

-- Substitutions from variables bound in cases
-- | Translate a CoreDecl
trDecl :: Var -> CoreExpr -> HaltM [Formula]
trDecl f e = local (\e -> e { fun = f , args = as , quant = as }) (trCase e')
  where -- Collect the arguments and the body expression
    as :: [Var]
    e' :: CoreExpr
    (as,e') = collectBinders e

trCase :: CoreExpr -> HaltM [Formula]
trCase e = case e of
  Case{} -> do
    -- Add a bottom case
    let Case scrutinee scrut_var _ty ((DEFAULT,[],def_expr):alts) = addBottomCase e

    -- Translate the scrutinee and add it to the substitutions
    local (\env -> env { subs = M.insert scrut_var scrutinee (subs env) }) $ do

        -- Translate the alternatives (mutually recursive with this function)
        formulae <- concatMapM (trAlt scrutinee) alts

        -- Collect the negative patterns
        let neg_constrs = map (invertAlt scrutinee) alts

        -- Translate the default formula which happens on the negative constraints
        def_formula <- local (\env -> env { constr = neg_constrs ++ constr env })
                             (trCase def_expr)

        -- Return both
        return (def_formula ++ formulae)
  _ -> do
    HaltEnv{..} <- ask
    let (subs',pos,neg) = collectConstr constr
    local (\env -> env { subs = subs `M.union` subs' }) $ do
      lhs <- trExpr (mkCoreApps (Var fun) (map Var args))
      rhs <- trExpr e
      tr_pos <- mapM (\(a,b) -> liftM2 (===) (trExpr a) (trExpr b)) pos
      tr_neg <- mapM (\(a,b) -> liftM2 (!=) (trExpr a) (trExpr b)) neg
      return [forall' (map mkVarName quant) ((tr_pos ++ tr_neg) =:=> (lhs === rhs))]

(=:=>) :: [Formula] -> Formula -> Formula
[] =:=> phi = phi
xs =:=> phi = foldr1 (/\) xs ==> phi

type Eqp = (CoreExpr,CoreExpr)

collectConstr :: [Constraint] -> (Map Var CoreExpr,[Eqp],[Eqp])
collectConstr cs = (M.fromList [ (x,e)     | Subst x e _bound <- cs ]
                   ,[ (lhs,rhs) | Equal lhs rhs _bound <- cs ]
                   ,[ (lhs,rhs) | lhs :=/= rhs <- cs ])


invertAlt :: CoreExpr -> CoreAlt -> Constraint
invertAlt scrutinee (con, bs, _) = case con of
  DataAlt data_con -> constraint
    where
      con_name   = dataConName data_con
      proj_binds = [ projExpr con_name i scrutinee | b <- bs | i <- [0..] ]
      constraint = scrutinee :=/= mkCoreConApps data_con proj_binds
  DEFAULT -> error "invertAlt on DEFAULT"
  _       -> error "invertAlt on LitAlt (literals not supported yet!)"


trAlt :: CoreExpr -> CoreAlt -> HaltM Formulae
trAlt scrutinee (con, bound, e) = case con of
  DataAlt data_con -> local (\env -> env { constr = new_constraint : constr env }) (trCase e)
    where
      rhs = mkCoreConApps data_con (map Var bound)
      new_constraint = case scrutinee of
                         Var x -> Subst x         rhs bound
                         _     -> Equal scrutinee rhs bound

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
trExpr :: CoreExpr -> HaltM Term
trExpr e = do
  HaltEnv{..} <- ask
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
--    Coercion{} -> trErr "coercions"
--    Tick{}     -> trErr "ticks"
  where trErr e s = error ("trExpr: no support for " ++ s ++ "\n"
                                          ++ showSDoc (pprCoreExpr e))

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
--idToStr = occNameString . nameOccName . idName

mkFun :: Var -> [Term] -> Term
mkFun = Fun . FunName . map toLower . idToStr

mkVarName :: Var -> VarName
mkVarName = VarName . (\(x:xs) -> toUpper x : xs) . idToStr

mkVar :: Var -> Term
mkVar = FVar . mkVarName

