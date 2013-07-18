-- | Some kind of z-encoding escaping
module Lang.Escape (escape) where

import qualified Data.Map as M
import Data.Maybe
import Data.Char

-- | Escaping
escape :: String -> String
escape = leading . concatMap (\c -> fromMaybe [c] (M.lookup c escapes))
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

leading :: String -> String
leading xs@(x:_) | isDigit x = '_':xs
                 | otherwise = xs
leading []                   = "_"
