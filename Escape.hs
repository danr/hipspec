-- | Some kind of z-encoding escaping
module Escape (escape) where

import qualified Data.Map as M
import Data.Maybe

-- | Escaping
escape :: String -> String
escape = concatMap (\c -> fromMaybe [c] (M.lookup c escapes))
  where
    escapes = M.fromList $ map (uncurry (flip (,)))
        [ ("za",'@')
        , ("z_",'\'')
        , ("z1",'(')
        , ("z2",')')
        , ("zb",'!')
        , ("zB",'}')
        , ("zc",':')
        , ("zC",'%')
        , ("zd",'$')
        , ("zE",'=')
        , ("zG",'>')
        , ("zh",'-')
        , ("zH",'#')
        , ("zi",'|')
        , ("zl",']')
        , ("zL",'<')
        , ("zm",',')
        , ("zn",'&')
        , ("zo",'.')
        , ("zp",'+')
        , ("zq",'?')
        , ("zr",'[')
        , ("zR",'{')
        , ("zs",'*')
        , ("zS",' ')
        , ("zt",'~')
        , ("zT",'^')
        , ("zv",'/')
        , ("zV",'\\')
        , ("zz",'z')
        ]
