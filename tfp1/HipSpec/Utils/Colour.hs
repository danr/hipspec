-- | Printing in colour and bold
module HipSpec.Utils.Colour where

data Colour = Red | Green | Blue | Pink | Yellow | Turquoise

-- | Print with colour
colour :: Colour -> String -> String
colour c s = fgcol ++ s ++ normal
  where
    fgcol :: String
    fgcol = "\ESC[0" ++ show (30+col2num) ++ "m"

    col2num :: Int
    col2num = case c of
      Red       -> 1
      Green     -> 2
      Yellow    -> 3
      Blue      -> 4
      Pink      -> 5
      Turquoise -> 7

-- | Print in bold
bold :: String -> String
bold = ("\ESC[1m" ++)

-- | Print normally
normal :: String
normal = "\ESC[0m"

