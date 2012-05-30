module Hip.FromHaskell.Vars
       (freeVars,freeVarss
       ,boundVars,boundVarss) where

import qualified Hip.Trans.Core as C
import Language.Haskell.Exts
import Hip.FromHaskell.Monad
import Hip.FromHaskell.Names

import Data.Set as S

import Control.Applicative hiding (empty)

class FV a where
  fv :: a -> FH (Set C.Name)

class BV a where
  bv :: a -> FH (Set C.Name)

-- The only exported functions
freeVars :: FV a => a -> FH [C.Name]
freeVars = fmap S.toList . fv

freeVarss :: FV a => [a] -> FH [C.Name]
freeVarss = fmap S.toList . fvs

boundVars :: BV a => a -> FH [C.Name]
boundVars = fmap S.toList . bv

boundVarss :: BV a => [a] -> FH [C.Name]
boundVarss = fmap S.toList . bvs

fvs :: FV a => [a] -> FH (Set C.Name)
fvs = fmap unions . mapM fv

bvs :: BV a => [a] -> FH (Set C.Name)
bvs = fmap unions . mapM bv

none :: FH (Set C.Name)
none = return empty

fvVar :: QName -> FH (Set C.Name)
fvVar qn = do
   n <- fromQName qn
   b <- lookupBind n
   -- debug $ "fvVar: on " ++ n ++ " bound: " ++ show b
   case b of
     Nothing       -> return (singleton n)
     Just (sn,fvs) -> return (singleton n `union` S.fromList fvs)

instance FV QOp where
  fv (QVarOp qn) = fvVar qn
  fv (QConOp{})  = none

instance FV Exp where
  fv ex = case ex of
      Var qn             -> fvVar qn
      Con{}              -> none
      Lit{}              -> none
      InfixApp e1 qop e2 -> unions <$> sequence [fv e1,fv qop,fv e2]
      RightSection qop e -> union <$> fv qop <*> fv e
      LeftSection  e qop -> union <$> fv e <*> fv qop
      App e1 e2          -> union <$> fv e1 <*> fv e2
      Lambda _loc ps el  -> difference <$> fv el <*> bvs ps
      If e1 e2 e3        -> unions <$> mapM fv [e1,e2,e3]
      Case e alts        -> union <$> fv e <*> fvs alts
      Paren e            -> fv e
      List es            -> fvs es
      Tuple es           -> fvs es

      Let bs e -> do bsf <- fv bs
                     bsb <- bv bs
                     v   <- fv e
                     return ((v `union` bsf) `difference` bsb)
      _        -> fatal $ "FV on exp " ++ show ex

instance FV Decl where
  fv d = case d of
    FunBind ms -> fvs ms
    PatBind loc p mtype rhs bs -> case p of
      PVar n -> fv (Match loc n [] mtype rhs bs)
      _      -> fatal $ "FV on top level pattern: " ++ show p
    _ -> debug ("Assumes decl: " ++ show d ++ " contains no FV") >> none

instance FV Match where
  fv (Match _loc n ps _mtype rhs bs) = do
     rhsvs <- fv rhs
     psvs  <- bvs ps
     bsvs  <- fv bs
     bsbv  <- bv bs
     -- Is this correct? Take all FV of the rhsvs and the bs, minus
     -- those from the patterns
     let r = (rhsvs `union` bsvs) `difference` (psvs `union` bsbv)
     -- debug $ show n ++ " fv: " ++ show r ++ " bsbv: " ++ show bsbv
     return r

instance FV Rhs where
  fv (UnGuardedRhs e) = fv e
  fv (GuardedRhss gs) = fvs gs

instance FV GuardedRhs where
  fv (GuardedRhs _loc stmts e) = union <$> fvs stmts <*> fv e

instance FV Alt where
  fv (Alt _loc pat guarded bs) = do
    patvs   <- bv pat
    guardvs <- fv guarded
    bsvs    <- fv bs
    bsbv    <- bv bs
    return $ (guardvs `union` bsvs) `difference` (patvs `union` bsbv)

instance FV GuardedAlts where
  fv (UnGuardedAlt e) = fv e
  fv (GuardedAlts gs) = fvs gs

instance FV GuardedAlt where
  fv (GuardedAlt _loc stmts e) = union <$> fvs stmts <*> fv e

-- Only interpreting Stmt as a guard!
instance FV Stmt where
  fv (Generator _loc p _e) = fatal $ "Pattern guards not supported: " ++ show p
  fv (Qualifier e)         = fv e
  fv (LetStmt bs)          = fv bs
  fv (RecStmt _stmts)      = fatal "Rec statements not supported"

instance FV Binds where
  fv (BDecls ds) = fvs ds
  fv (IPBinds{}) = warn "Not handling implicit arguments" >> none

-- Bound Variables ------------------------------------------------------------

retName :: Name -> FH (Set C.Name)
retName = return . singleton . fromName

instance BV Decl where
  bv d = case d of
    FunBind ms -> bvs ms
    PatBind _loc p _mtype _rhs _bs -> case p of
      PVar n -> retName n
      _ -> fatal $ "BV on top level pattern: " ++ show p
    _ -> debug ("Assumes decl: " ++ show d ++ " contains no BV") >> none

instance BV Match where
  -- Handle binds?
  bv (Match _loc n ps _mtype _rhs _bs) = union <$> retName n <*> bvs ps

instance BV Binds where
  bv (BDecls ds) = bvs ds
  bv (IPBinds{}) = warn "Not handling implicit arguments" >> none

-- These are not really free vars, they are bound vars, but they work
-- the same way
instance BV Pat where
  bv pat = case pat of
    PVar n              -> retName n
    PLit{}              -> none
    PNeg{}              -> none
    PInfixApp p1 _qn p2 -> union <$> bv p1 <*> bv p2
    PApp _qn ps         -> bvs ps
    PTuple ps           -> bvs ps
    PList ps            -> bvs ps
    PParen p            -> bv p
    PWildCard           -> none
    _                   -> fatal $ "FV on pat " ++ show pat