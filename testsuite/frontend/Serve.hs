module Main where

import Network.Wai.Middleware.RequestLogger (logStdout)
import Network.Wai.Middleware.Static
import Web.Scotty

main = scotty 2999 $ do

    middleware logStdout
    middleware static
    middleware $ staticPolicy (addBase "..")

