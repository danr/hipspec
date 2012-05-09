-- (c) Dan Rosén 2012
{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
module Halt.Trans(translate) where

import BasicTypes
import CoreSubst
import CoreSyn
import CoreUtils
import DataCon
import FastString
import Id
import Literal
import Outputable
import TyCon
import TysWiredIn
import Unique
import UniqSupply

import Halt.Names
import Halt.Util
import Halt.Monad
import Halt.Conf
import Halt.Data

import FOL.Syn hiding ((:==))

import qualified Data.Map as M
import Data.Char (toUpper,toLower,isAlpha)
import Data.List (intercalate)

import Control.Monad.Reader
import Control.Monad.Writer

-- | Takes a CoreProgram (= [CoreBind]) and makes FOL translation from it
--   TODO: Register used function pointers
translate :: UniqSupply -> HaltConf -> [TyCon] -> [CoreBind] -> ([FDecl],[String])
translate us conf@(HaltConf{..}) ty_cons program =
  let -- Remove the unnecessary SCC information
      binds :: [(Var,CoreExpr)]
      binds = flattenBinds program

      names :: Names
      names = fst (mkNames us)

      ty_cons_with_builtin :: [TyCon]
      ty_cons_with_builtin = listTyCon : boolTyCon : unitTyCon
                           : map (tupleTyCon BoxedTuple) [2..4]
                             -- ^ choice: only tuples up to 4 supported
                           ++ ty_cons

      -- Arity of each function (Arities from other modules are also needed)
      arities :: ArityMap
      arities = M.fromList $ [ (idName v,exprArity e) | (v,e) <- binds ]
                          ++ dataArities ty_cons_with_builtin

      -- Translate each declaration
      -- TODO : Make these return Decl?
      translated :: HaltM [Formula]
      translated = concatMapM (uncurry trDecl) binds

      formulae :: [Formula]
      msgs :: [String]
      (formulae,msgs) = runWriter (runHaltM translated `runReaderT`
                                            initEnv names conf arities)

  in  (mkProjs conf ty_cons_with_builtin ++
       mkDiscrim conf ty_cons_with_builtin ++
       [ FDecl (if use_cnf then CNF else Axiom) (show n) phi
       | phi <- formulae
       | n <- [(0 :: Int)..]]
      ,msgs ++ [ showSDoc (ppr k) ++ "(" ++ show (getUnique k) ++ "):" ++ show v | (k,v) <- M.toList arities])

-- | Translate a CoreDecl or a Let
trDecl :: Var -> CoreExpr -> HaltM [Formula]
trDecl f e = do
    write $ "Translating " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
    local (\env -> env { fun = f
                       , args = map Var as ++ args env
                       , quant = as ++ quant env}) (trCase e')
  where -- Collect the arguments and the body expression
    as :: [Var]
    e' :: CoreExpr
    (_ty,as,e') = collectTyAndValBinders e
    -- Dangerous? Type variables are skipped for now.

-- | The arity of an expression if it is a lambda
exprArity :: CoreExpr -> Int
exprArity e = length as
  where (_,as,_) = collectTyAndValBinders e

-- | Translate a case expression
trCase :: CoreExpr -> HaltM [Formula]
trCase e = case e of
    Case{} -> do
        -- Add a bottom case
        Case scrutinee _scrut_var _ty ((DEFAULT,[],def_expr):alts) <- addBottomCase e

        write $ "Case on " ++ showExpr scrutinee

        -- Translate the scrutinee and add it to the substitutions
        -- We should do something about the scrutinee var here really
        -- local (extendSubs (M.singleton scrut_var (error "scrutinee"))) $ do
        -- TODO: Test case that triggers this error

        HaltConf{..} <- asks conf

        min_formula <-
            if not use_min then return [] else do
                m_tr_constr <- trConstraints
                case m_tr_constr of
                    Nothing -> return []
                    Just tr_constr -> do
                        lhs <- trLhs
                        tr_scrut <- trExpr scrutinee
                        let constr = minPred lhs : tr_constr
                        qvars <- asks quant
                        let res = implies use_cnf constr (minPred tr_scrut)
                            quantified = (not use_cnf ? forall' (map mkVarName qvars)) res
                        return [quantified]

        -- Translate the alternatives (mutually recursive with this
        -- function)
        alt_formulae <- concatMapM (trAlt scrutinee) alts

        -- Collect the negative patterns
        let neg_constrs = map (invertAlt scrutinee) alts

        -- Translate the default formula which happens on the negative
        -- constraints
        def_formula <- local (\env -> env { constr = neg_constrs ++ constr env })
                             (trCase def_expr)

        return ((use_min ? (min_formula ++)) (alt_formulae ++ def_formula))
    _ -> do
        HaltEnv{fun,quant} <- ask
        HaltConf{..} <- asks conf
        write $ "At the end of " ++ idToStr fun ++ "'s branch: " ++ showExpr e
        m_tr_constr <- trConstraints
        case m_tr_constr of
            Nothing -> return []
            Just tr_constr -> do
                lhs <- trLhs
                rhs <- trExpr e
                let common_var = VarName "C"
                    common | common_min = FVar common_var
                           | otherwise  = lhs
                    constr = [ common === lhs | common_min ] ++
                             [ minPred common | use_min ] ++
                             tr_constr
                    phi | common_min = common === rhs
                        | otherwise  = lhs === rhs
                let res = implies use_cnf constr phi
                    quant' | common_min = common_var : map mkVarName quant
                           | otherwise  = map mkVarName quant
                    quantified | use_cnf       = res
                               | otherwise = forall' quant' res
                return [quantified]


trLhs :: HaltM Term
trLhs = do
    HaltEnv{fun,args} <- ask
    mkFun fun <$> mapM trExpr args

trConstraints :: HaltM (Maybe [Formula])
trConstraints = do
    HaltEnv{constr} <- ask
    write $ "Constraints: " ++ concatMap ("\n    " ++) (map show constr)
    if conflict constr
        then write "  Conflict!" >> return Nothing
        else Just <$> mapM trConstr constr

conflict :: [Constraint] -> Bool
conflict cs = or [ cheapExprEq e1 e2 && con_x == con_y
                 | Equality   e1 con_x _ <- cs
                 , Inequality e2 con_y <- cs
                 ]
  where
    cheapExprEq :: CoreExpr -> CoreExpr -> Bool
    cheapExprEq (Var x) (Var y) = x == y
    cheapExprEq (App e1 e2) (App e1' e2') = cheapExprEq e1 e2 &&
                                            cheapExprEq e1' e2'
    cheapExprEq _ _ = False

trConstr :: Constraint -> HaltM Formula
trConstr (Equality e data_con bs) = do
    lhs <- trExpr e
    rhs <- mkFun (dataConWorkId data_con) <$> mapM trExpr bs
    return $ lhs === rhs
trConstr (Inequality e data_con) = do
    lhs <- trExpr e
    let rhs = mkFun (dataConWorkId data_con)
                    [ projFun (idName $ dataConWorkId data_con) i lhs
                    | i <- [0..dataConSourceArity data_con-1] ]
    return $ lhs != rhs

invertAlt :: CoreExpr -> CoreAlt -> Constraint
invertAlt scrut_exp (con, _bs, _) = case con of
  DataAlt data_con -> Inequality scrut_exp data_con
  DEFAULT          -> error "invertAlt on DEFAULT"
  _                -> error "invertAlt on LitAlt (literals not supported yet!)"


trAlt :: CoreExpr -> CoreAlt -> HaltM Formulae
trAlt scrut_exp (con, bound, e) = do
  HaltEnv{quant} <- ask
  case con of
    DataAlt data_con -> do
        case scrut_exp of
            Var x | x `elem` quant -> do
                let tr_pat = foldl App (Var (dataConWorkId data_con)) (map Var bound)
                    s = extendIdSubst emptySubst x (tr_pat)
                    e' = substExpr (text "trAlt") s e
                local (substContext s . pushQuant bound . delQuant x) (trCase e')
            _ -> local (pushConstraint (Equality scrut_exp data_con (map Var bound))
                       . pushQuant bound)
                       (trCase e)

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
addBottomCase :: CoreExpr -> HaltM CoreExpr
addBottomCase (Case scrutinee binder ty alts) = do
    bottomCon <- getConOf Bottom
    bottomVar <- Var <$> getIdOf Bottom
    let -- _|_ -> _|_
        -- Breaks the core structure by having a new data constructor
        bottomAlt :: CoreAlt
        bottomAlt = (DataAlt bottomCon, [], bottomVar)

        -- DEFAULT -> _|_
        defaultBottomAlt :: CoreAlt
        defaultBottomAlt = (DEFAULT, [], bottomVar)
    -- Case expressions have an invariant that the default case is always first.
    return $ Case scrutinee binder ty $ case findDefault alts of
         (as,Just def) -> (DEFAULT, [], def):bottomAlt:as
         (as,Nothing)  -> defaultBottomAlt:as
addBottomCase _ = error "addBottomCase on non-case expression"

-- | Translate expressions, i.e. not case (nor let/lambda)
trExpr :: CoreExpr -> HaltM Term
trExpr e = do
    HaltEnv{..} <- ask
    let isFunction x = case M.lookup (idName x) arities of
                          Just i  -> i > 0
                          Nothing -> False
    case e of
        Var x | x `elem` quant -> return (mkVar x)
              | isFunction x   -> return (mkPtr x)
              | otherwise      -> return (mkFun x [])
        App{} -> do
          write $ "App on " ++ showExpr e
          case second trimTyArgs (collectArgs e) of
            (Var x,es)
               | Just i <- M.lookup (idName x) arities -> do
                   write $ idToStr x ++ " has arity " ++ show i
                   if i > length es
                       then foldFunApps (mkPtr x) <$> mapM trExpr es
                       else do
                           let (es_inner,es_after) = splitAt i es
                           inner <- mkFun x <$> mapM trExpr es_inner
                           foldFunApps inner <$> mapM trExpr es_after
            (f,es) -> do
               write $ "Collected to " ++ showExpr f
                           ++ concat [ "(" ++ show (getUnique (idName x)) ++ ") " | let Var x = f ]
                           ++ " on " ++ intercalate "," (map showExpr es)
               foldFunApps <$> trExpr f <*> mapM trExpr es
        Lit (MachStr s) -> do
          write $ "String to constant: " ++ unpackFS s
          return $ Fun (FunName "string") [Fun (FunName (unpackFS s)) []]

        Case{}      -> trErr "case" -- trCaseExpr e
        Let{}       -> trErr "let"  -- trLet bind e'
        Cast e' _   -> do
          write $ "Ignoring cast: " ++ showExpr e
          trExpr e'

        Lit{}      -> trErr "literals"
        Type{}     -> trErr "types"
        Lam{}      -> trErr "lambdas"
        Coercion{} -> trErr "coercions"
        Tick{}     -> trErr "ticks"
  where trErr s = error ("trExpr: no support for " ++ s ++ "\n" ++ showExpr e)

trimTyArgs :: [CoreArg] -> [CoreArg]
trimTyArgs = filter (not . isTyArg)
  where
    isTyArg Type{} = True
    isTyArg _      = False

foldFunApps :: Term -> [Term] -> Term
foldFunApps = foldl (\x y -> Fun (FunName "app") [x,y])


mkPtr :: Var -> Term
mkPtr = (`Fun` []) . FunName . (++ "ptr") . map toLower . idToStr

mkVarName :: Var -> VarName
mkVarName = VarName . capInit . idToStr
  where
    capInit (x:xs) | isAlpha x = toUpper x : xs
                   | otherwise = 'Q':x:xs
                        -- ^ needs escaping here
                        --   example: (>) as an argument to a sortBy function
    capInit "" = "Q"

mkVar :: Var -> Term
mkVar = FVar . mkVarName

