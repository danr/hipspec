module Hip.Trans.Run where

import Language.TPTP.Pretty
import Hip.Trans.Parser
import Hip.Trans.Latex
import Hip.Trans.ToTPTP
import Hip.Trans.Core
import Hip.Trans.Pretty
import qualified Language.TPTP as T

import Control.Monad

import System.Environment

main :: IO ()
main = do
  file:rest <- getArgs
  ds <- parseFile file
  let (funcAxiomsWithDef,extraAxioms,debug) = toTPTP ds
      axioms = concatMap snd funcAxiomsWithDef ++ extraAxioms
  -- Verbose output
  when ("-v" `elem` rest)    (mapM_ putStrLn debug)
  -- Supress ordinary output
  when ("-s" `notElem` rest) (putStrLn (prettyTPTP axioms))
  -- Latex output
  when ("-l" `elem` rest) $ do
      putStrLn (latexHeader file extraAxioms)
      mapM_ (putStr . uncurry latexDecl) funcAxiomsWithDef
      putStrLn latexFooter


latexHeader :: String -> [T.Decl] -> String
latexHeader file fs = unlines $
  ["\\documentclass{article}"
  ,"\\usepackage[a4paper]{geometry}"
  ,"\\usepackage{amsmath}"
  ,"\\begin{document}"
  ,"\\title{" ++ file ++ "}"
  ,"\\maketitle"
  ,"\\section{Datatypes and pointers}"
  ,"\\begin{align*}"
  ]
  ++ map runLatex fs ++
  ["\\end{align*}"
  ,"\\newpage"
  ]

latexDecl :: Decl -> [T.Decl] -> String
latexDecl Data{}          _  = error "latexDecl on data"
latexDecl d@(Func fn _ _) fs = unlines $
  ["\\section{" ++ fn ++ "}"
  ,""
  ,"\\subsection{Definition}"
  ,""
  ,"\\begin{verbatim}"
  ,prettyCore d
  ,"\\end{verbatim}"
  ,""
  ,"\\subsection{Axioms}"
  ,""
  ,"\\begin{align*}"
  ]
  ++ map runLatex fs ++
  ["\\end{align*}"
  ,"\\newpage"
  ]

latexFooter :: String
latexFooter = "\\end{document}"