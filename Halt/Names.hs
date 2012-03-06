module Halt.Names where

import Name
import CoreSyn
import DataCon
import Id
import Unique
import SrcLoc

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
projName :: Int -> Name
projName =
  let vars :: [Name]
      vars = [ mkInternalName (mkPreludeMiscIdUnique (i + 1)) -- (error ("projName" ++ show i ++ ": unique"))
                              (mkOccName dataName ("p" ++ show i))
                              wiredInSrcSpan
             | i <- [(0 :: Int)..] ]

  in \i -> vars !! i

-- | The projection variables
projVar :: Int -> CoreExpr
projVar i = Var (mkVanillaGlobal (projName i) (error "projVar: type"))

-- | Projects an expression
projExpr :: Int -> CoreExpr -> CoreExpr
projExpr i e = App (projVar i) e
