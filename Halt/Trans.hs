-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, PatternGuards #-}
module Halt.Trans where

import PprCore

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

-- The translation monad, fst is the argument variables to a function,
-- arity map is the map of arities
type HaltM = Reader ([Var],ArityMap)

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
--   Right now unsound an incomplete as nothing is done for data types,
--   this is just a sketch
--   TODO: Top level-lift Let
--   TODO: Register used function pointers
--   TODO: Assumes only nested case expression at top level of the body
--         of a function. Possible fix: top level lift all other case expressions
translate :: [CoreBind] -> [FDecl]
translate program =
  let -- Let-lift the program
      liftedProgram :: [CoreBind]
      liftedProgram = {- liftProgram -} program

      -- Remove the unnecessary SCC information
      binds :: [(Var,CoreExpr)]
      binds = flattenBinds liftedProgram

      -- Arity of each function (Arities from other modules are also needed)
      arities :: ArityMap
      arities = M.fromList [(v,length (fst (collectBinders e))) | (v,e) <- binds ]

      -- Translate each declaration
      translated :: HaltM Formulae
      translated = concat `fmap` sequence [ trDecl v e | (v,e) <- binds ]

  in  [ FDecl Axiom ("decl" ++ show n) phi | phi <- translated `runReader` ([],arities)
                                           | n <- [(0 :: Int)..] ]

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

{-

  Currently we do translation by only using projection functions.

  f x = case g x of
          K a b -> h a x

  The above definion of f is translated to these two axioms

  I.  forall x . g(x) = k(p0(g(x)),p1(g(x)))
              => f(x) = h(p0(g(x)),x)
  II. forall x . g(x) /= k(p0(g(x)),p1(g(x)))
              => f(x) = _|_

  Side note: Another possible translation of the first axiom is

             I.   forall x a b . g(x) = k(a,b) => f(x) = h(a,x)

             It would be interesting to have both translations and see
             how the performance differs when using theorem provers.
             TODO: Make a toggle for this

  When using projections as above, we collect constraints and
  substitutions as we dig deeper into case expressions.
  Constraints:   g(x) = k(p0(g(x)),p1(g(x)))
  Substitutions: a = p0(g(x)), b = p1(g(x))
  The substitutions are local for a case alternative, but the
  constraints are used for the DEFAULT case.

  -}

-- Substitutions from variables bound in cases
type Subs        = Map Var      CoreExpr

-- Constraints from case expressions to results, under a substitution
data Constraint  = Constraint { constrSub :: Subs
                              , constrLhs , constrRhs :: CoreExpr
                              }
type Constraints = [Constraint]

-- | The empty substitution
noSubs :: Subs
noSubs = M.empty

-- | The empty constraints
noConstraints :: Constraints
noConstraints = []

-- | Translate a CoreDecl
trDecl :: Var -> CoreExpr -> HaltM Formulae
trDecl f e =
  let -- Collect the arguments and the body expression
      as :: [Var]
      body :: CoreExpr
      (as,body) = collectBinders e

  in  trBody f as body noSubs noConstraints

-- | Translate a body, i.e, case statements eventually ending in expressions
trBody :: Var -> [Var] -> CoreExpr -> Subs -> Constraints -> HaltM Formulae
trBody f as e subs cons = local (first (const as)) $ case e of
  Case{} -> do let -- Add the bottom case, afterwards there is a default case first
                   Case scrutinee scrut_var _ty ((DEFAULT,[],def_expr):alts) = addBottomCase e

                   -- Translate the scrutinee and add it to the substitutions
                   subs' :: Subs
                   subs' = M.insert scrut_var scrutinee subs

               -- Translate the non-default alternatives, getting formulas and constraints.
               -- These constraints should be in negative position
               (alt_formulae,cons') <- runWriterT (concat <$> mapM (trAlt f as scrut_var subs' cons) alts)
               (:alt_formulae) <$> trFunctionDecl def_expr (allEqual cons ++ allUnequal cons')
  _ -> do (:[]) <$> trFunctionDecl e (allEqual cons)
  where
    -- Translates a core expression with positioned constraints to a formula, i.e.
    -- If the constraints are [ (Equal, x, e1), (Unequal, y, e2) ], and the arguments are [x,y,z], and
    -- the expression is e and the function is f, we get:
    -- forall x y z . x = e1 & y /= e2 => f(x,y,z) = e
    trFunctionDecl :: CoreExpr -> [(Position,Constraint)] -> HaltM Formula
    trFunctionDecl expr cons_ = do
        lhs    <- trExpr subs expr
        as'    <- mapM (trExpr subs . Var) as
        constr <- trConstraints cons_
        return $ forall' (map mkVarName as)
                         (constr (mkFun f as' === lhs))

-- | Translate an alternative from a case expression
--   An alternative generates a constraint from that construction with the current substitution.
trAlt :: Var -> [Var] -> Var -> Subs -> Constraints -> CoreAlt
      -> WriterT Constraints HaltM Formulae
trAlt f as scrut_var subs cons (con, bs, e) =
  case con of
    DataAlt data_con ->
      let con_name       = dataConName data_con
          con_fol_repr   = [(b,projExpr i (Var scrut_var)) | b <- bs | i <- [0..] ]
          subs'          = M.union subs (M.fromList con_fol_repr)
          new_constraint = Constraint subs' (Var scrut_var) (mkConApp data_con (map snd con_fol_repr))
      in  do tell [new_constraint]
             lift $ trBody f as e subs' (new_constraint:cons)
    DEFAULT -> error "trAlt on DEFAULT"
    _       -> error "trAlt on LitAlt (literals no support yet!)"


-- | Translate an expression, i.e. not case statements. Substitutions are followed.
trExpr :: Subs -> CoreExpr -> HaltM Term
trExpr subs e = do
  as <- asks fst
  case e of
    Var x | Just e' <- M.lookup x subs -> trExpr subs e'
          | x `elem` as                -> return (mkVar x)
          | otherwise                  -> return (mkFun x [])
    App{} -> case second trimTyArgs (collectArgs e) of
                    -- TODO : Use the arities and add appropriate use of app
                    (Var x,es) -> mkFun x <$> mapM (trExpr subs) es
                    (f,es)     -> foldl (\x y -> Fun (FunName "ptrApp") [x,y])
                                     <$> trExpr subs f
                                     <*> mapM (trExpr subs) es
    Lit (MachStr s) -> return (Fun (FunName "string") [Fun (FunName (unpackFS s)) []])
    Lit{}      -> trErr e "literals"
    Cast{}     -> trErr e "casts"
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

data Position = Equal | Unequal
  deriving (Eq,Show)

allEqual :: Constraints -> [(Position,Constraint)]
allEqual = map ((,) Equal)

allUnequal :: Constraints -> [(Position,Constraint)]
allUnequal = map ((,) Unequal)

trConstraints :: [(Position,Constraint)] -> HaltM (Formula -> Formula)
trConstraints []   = return id
trConstraints cons = (==>) . foldr1 (/\) <$> mapM (uncurry trConstraint) cons
  where
    trConstraint :: Position -> Constraint -> HaltM Formula
    trConstraint eq (Constraint subs lhs rhs) = equals <$> trExpr subs lhs <*> trExpr subs rhs
      where
        equals = if eq == Unequal then (!=) else (===)

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
