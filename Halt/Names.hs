module Halt.Names where

import CoreSyn
import DataCon
import Id
import Name
import Outputable
import SrcLoc
import Unique

-- | Short representation of an Id/Var to String
idToStr :: Id -> String
idToStr = showSDocOneLine . ppr . maybeLocaliseName . idName
  where
    maybeLocaliseName n | isSystemName n = n
                        | otherwise      = localiseName n


-- | The bottom name, did not know what Name to pick so I tried System Name
bottomName :: Name
bottomName = mkInternalName (mkPreludeMiscIdUnique 0) -- error "bottomName: unique")
                            (mkOccName dataName "bottom")
                            wiredInSrcSpan

-- | The constructor for bottom
bottomCon :: DataCon
bottomCon = mkDataCon bottomName
                      False -- infix
                      []    -- strictness
                      []    -- records
                      []    -- univ.q. ty vars
                      []    -- ext.q. ty vars
                      []    -- gadt equalities
                      []    -- theta types
                      []    -- argument types
                      (error "bottomCon: result type (Type)")
                      (error "bottomCon: repr type constructor (TyCon)")
                      []    -- stupid theta types
                      (DCIds Nothing
                             bottomId)

-- | The bottom identifier
bottomId :: Id
bottomId = mkVanillaGlobal bottomName (error "bottomVar: type")

-- | The bottom expression
bottomVar :: CoreExpr
bottomVar = Var bottomId

{-
-- | The ptrApp name, did not know what Name to pick so I tried System Name
ptrAppName :: Name
ptrAppName = mkSystemName (mkPreludeMiscIdUnique 0)
                          (mkOccName dataName "ptrApp")

-- | The ptrApp identifier
ptrAppId :: Id
ptrAppId = mkVanillaGlobal ptrAppName (error "ptrAppVar: type")

-- | The ptrApp expression
ptrAppVar :: CoreExpr
ptrAppVar = Var ptrAppId
-}

-- | The projection names. How to get uniques?
projName :: Name -> Int -> Name
projName con_name =
  let vars :: [Name]
      vars = [ mkInternalName
                 (mkPreludeMiscIdUnique (i + 1))
                 (mkOccName dataName
                     (showSDoc (ppr $ localiseName con_name) ++ show i))
                 wiredInSrcSpan
             | i <- [(0 :: Int)..] ]

  in \i -> vars !! i

-- | The projection variables
projVar :: Name -> Int -> CoreExpr
projVar con_name i = Var (mkVanillaGlobal (projName con_name i) (error "projVar: type"))

-- | Projects an expression
projExpr :: Name -> Int -> CoreExpr -> CoreExpr
projExpr con_name i = App (projVar con_name i)
