module Hip.Messages
       (Source(..)
       ,Msg()
       ,msgSource
       ,msgString
       ,dbfhMsg
       ,dbfolMsg
       ,dbproofMsg
       ,warnMsg
       ,isWarning
       ,sourceIs
       ) where

data Source = FromHaskell | Trans | MakeProof
  deriving (Eq,Ord,Show)

data Msg = Debug   { msgSource :: Source , msgString :: String }
         | Warning { msgString :: String }
  deriving (Eq,Ord)

instance Show Msg where
  show (Warning s) = "warning: " ++ s
  show (Debug _ s) = s

dbfhMsg,dbfolMsg,dbproofMsg,warnMsg :: String -> Msg
dbfhMsg    = Debug   FromHaskell
dbfolMsg   = Debug   Trans
dbproofMsg = Debug   MakeProof
warnMsg    = Warning

isWarning :: Msg -> Bool
isWarning Warning{} = True
isWarning _         = False

sourceIs :: Source -> Msg -> Bool
sourceIs s (Debug s' _) = s == s'
sourceIs _ _            = False