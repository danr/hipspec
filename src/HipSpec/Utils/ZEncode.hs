-- | Z-encoding
module HipSpec.Utils.ZEncode (zencode) where

import Data.Char
import qualified Data.Map as M
import Data.Maybe

-- | Escaping via z-encoding
--
--   GHC's encoder in Encoding could be used, but it escapes underscores which
--   is a bit annoying
zencode :: String -> String
zencode = leading . concatMap (\ c -> fromMaybe [c] (M.lookup c escapes))
  where
    escapes = M.fromList $ map (uncurry (flip (,)))
        [ ("ZL",'(')
        , ("ZR",')')
        , ("ZC",':')
        , ("ZM",'[')
        , ("ZN",']')
        , ("ZC",',')
        , ("ZZ",'Z')

        , ("zB",'}')
        , ("zR",'{')

        , ("z_",'\'')
        , ("za",'@')
        , ("zb",'!')
        , ("zc",'%')
        , ("zd",'$')
        , ("ze",'=')
        , ("zf",' ')
        , ("zg",'>')
        , ("zh",'#')
        , ("zi",'|')
        , ("zk",'^')
        , ("zm",'-')
        , ("zn",'&')
        , ("zo",'.')
        , ("zp",'+')
        , ("zq",'?')
        , ("zs",'*')
        , ("zt",'~')
        , ("zv",'/')
        , ("zx",'\\')
        , ("zz",'<')
        , ("zz",'z')
        ]

    leading :: String -> String
    leading xs@(x:_) | isDigit x = '_':xs
                     | otherwise = xs
    leading []                   = "_"
