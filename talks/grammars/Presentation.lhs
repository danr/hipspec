\documentclass[ignorenonframetext,]{beamer}

%include polycode.fmt

%format ==>    = "\Longrightarrow"
%format forall = "\forall"
%format zo'u   = "."
%format /=     = "\neq"
%format ==     = "="
%format quad   = "\quad\quad"

%format s1
%format s2
%format t1
%format t2


%format a1
%format a2
%format a3
%format b1
%format b2
%format b3
%format x0
%format x1
%format x2
%format x3
%format an     = "\mathit{a_n}"
%format bn     = "\mathit{b_n}"
%format xn     = "\mathit{x_n}"
%format xm     = "\mathit{x_m}"
%format A1
%format A2
%format A3
%format B1
%format B2
%format B3
%format X1
%format X2
%format X3
%format An     = "\mathit{A_n}"
%format Bn     = "\mathit{B_n}"
%format Xn     = "\mathit{X_n}"

%format xN     = "\mathit{x^n}"
%format yN     = "\mathit{y^n}"
%format y2N    = "\mathit{y^{2n}}"

%format U      = "\cup"

%format epsilon = "\epsilon"

%format IH1





\setbeamertemplate{caption}[numbered]
\setbeamertemplate{caption label separator}{:}
\setbeamercolor{caption name}{fg=normal text.fg}
\usepackage{amssymb,amsmath}
\usepackage{ifxetex,ifluatex}
\usepackage{fixltx2e} % provides \textsubscript
\usepackage{lmodern}
\ifxetex
  \usepackage{fontspec,xltxtra,xunicode}
  \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
  \newcommand{\euro}{€}
\else
  \ifluatex
    \usepackage{fontspec}
    \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
    \newcommand{\euro}{€}
  \else
    \usepackage[T1]{fontenc}
    \usepackage[utf8]{inputenc}
      \fi
\fi
% use upquote if available, for straight quotes in verbatim environments
\IfFileExists{upquote.sty}{\usepackage{upquote}}{}
% use microtype if available
\IfFileExists{microtype.sty}{\usepackage{microtype}}{}

% Comment these out if you don't want a slide with just the
% part/section/subsection/subsubsection title:
\AtBeginPart{
  \let\insertpartnumber\relax
  \let\partname\relax
  \frame{\partpage}
}
\AtBeginSection{
  \let\insertsectionnumber\relax
  \let\sectionname\relax
  \frame{\sectionpage}
}
\AtBeginSubsection{
  \let\insertsubsectionnumber\relax
  \let\subsectionname\relax
  \frame{\subsectionpage}
}

\newcommand{\vp}{\pause{\vspace{-2\baselineskip}}}

\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt plus 2pt minus 1pt}
\setlength{\emergencystretch}{3em}  % prevent overfull showes
\setcounter{secnumdepth}{0}

% Showing that a Context Free Grammar is unambiguous can be expressed as an
% induction problem over a functional program. The corresponding program uses
% plain, simple structural induction. On the other hand, the proof of unambiguity
% can require complex lemmas about functions that are not present in the original
% program.  This is way beyond what HipSpec can do automatically, so the demos
% will show HipSpec used in a more interactive setting.

\title{Context Free Grammars and Induction}
\subtitle{Second Inductive Theorem Proving Festival, 2015}
\institute{Chalmers University of Technology}

\author{Dan Ros\'en}
\date{} % June 4, 2013}

\begin{document}

\begin{frame}
\maketitle
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Context Free Grammars and Induction}

\begin{itemize}
\item Unambiguity proving of a CFG is an induction problem
\item Recursion only by simple structural induction
\item Can require very complicated lemmas
\end{itemize}

\end{frame}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Expression grammar}

> E  ::=  ( E + E ) | x | y

\vp

> data E = Plus E E | EX | EY
> data Token = C | D | P | X | Y
>
> show  :: E -> [Token]
> show  (Plus a b)  = [C] ++ show a ++ [P] ++ show b ++ [D]
> show  EX          = [X]
> show  EY          = [Y]

\vp

> forall s t zo'u show s = show t ==> s = t
> forall s t zo'u s /= t ==> show s /= show t

\vspace{2\baselineskip}

\end{frame}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Expression unambiguity, step case}

> show  (Plus a b)  = [C] ++ show a ++ [P] ++ show b ++ [D]
> show  EX          = [X]
> show  EY          = [Y]
>
> forall s t zo'u show s = show t ==> s = t
>
> assumption:  show (Plus s1 s2) = show (Plus t1 t2)
> goal:        Plus s1 s2 = Plus t1 t2

\vp

> show s1 ++ [P] ++ show s2 = show t1 ++ [P] ++ show t2

\vp

> forall a b u v zo'u  show a ++ u = show b ++ v ==> a == b && u == v

\vspace{4\baselineskip}

\end{frame}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Expression unambiguity, lemma}

% > show  (Plus a b)  = [C] ++ show a ++ [P] ++ show b ++ [D]
% > show  EX          = [X]
% > show  EY          = [Y]

> forall a b u v zo'u  show a ++ u = show b ++ v ==> a == b && u == v

\vp

> IH1: forall u' v' zo'u show a1 ++ u' = show b1 ++ v' ==> a1 == b1 && u' == v'
> assumption:  show (Plus a1 a2) ++ u = show (Plus b1 b2) ++ v
> goal:        Plus a1 b1 = Plus a2 b2 && u == v

\vp

>    [C] ++ show a1 ++ [P] ++ show a2 ++ [D] ++ u
> =  [C] ++ show b1 ++ [P] ++ show b2 ++ [D] ++ v

\vp


>    show a2 ++ [D] ++ u = show b2 ++ [D] ++ v

\vspace{4\baselineskip}

\end{frame}


% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \begin{frame}[fragile]{Similar grammar}
%
% > E  ::=  T + T  | T
% > T  ::=  ( E )  | x  | y
%
% Can we use the same heuristic?
%
% \end{frame}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{A more difficult example}

> S  ::=  A | B
> A  ::=  x A y     |   z
> B  ::=  x B y y   |   z
>
> { xN z yN | n > 0 } U { xN z y2N | n > 0 }

Not LR(k) for any k

\vspace{4\baselineskip}

\end{frame}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Injectivity digression}

easy:

> forall xs ys zs zo'u  xs ++ ys == xs ++ zs ==> ys == zs

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Injectivity digression}

``hard'':

> forall xs ys zs zo'u  xs ++ zs == ys ++ zs ==> xs == ys

\vp

> IH: forall xs ys zo'u  xs ++ cs == ys ++ cs ==> xs == ys
>
> assume:  as ++ c:cs == bs ++ c:cs
>
> show:    as ++ bs

\vp

> assumption:  (as ++ [c]) ++ cs  == (bs ++ [c]) ++ cs
> by IH:       as ++ [c]          == bs ++ [c]

\vp

> forall xs ys z zo'u  xs ++ [z] == ys ++ [z] ==> xs == ys

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Injectivity lemma}

> assume:  (a:as) ++ [c] == (b:bs) ++ [c]
> show:    a:as == b:bs

> IH:      as ++ [c] == bs ++ [c] ==> as == bs

> (a:as) ++ [c] == (b:bs) ++ [c]
> a:(as ++ [c]) == b:(bs ++ [c])
> a == b && as ++ [c] == bs ++ [c]
> a == b && as == bs

\end{frame}

\begin{frame}[fragile]{Required Lemmas (besides injectivity and trivialities)}

> S  ::=  A | B
> A  ::=  x A y     |   z
> B  ::=  x A y y   |   z
> { xN z yN | n > 0 } U { xN z y2N | n > 0 }
>
> count x (xs ++ ys) = count x xs + count  x ys
> count x A = count y A                    count x A > 0
> double (count x B) = count y B           count y A > 0
>                                          count x B > 0
>                                          count y B > 0
> double x /= x for x > 0, using:  x + y = x + z => y = z
>                                  double x = x + x

\vspace{4\baselineskip}

\end{frame}


\begin{frame}[fragile]{Successful run}
{\tiny
\begin{verbatim}
       Proved:
           count Z (showB x) = S Zero
           count Z (showA x) = S Zero
           count Y (showA x) = count X (showA x)
           double (count X (showB x)) = count Y (showB x)
           nonZero (count x (showB y)) = True
           nonZero (count x (showA y)) = True
           count x xs + count x ys = count x (xs ++ ys)
           double (count x xs) = count x (xs ++ xs)
           count x (xs ++ ys) = count x (ys ++ xs)
           (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
           (x + y) + z = x + (y + z)
           double x = x + x
           x + y = y + x
           xs ++ [] = xs
           x + Zero = x
           unambigS {- showS u == showS v => u == v -}
           unambigB {- showB u == showB v => u == v -}
           plusInjL {- y+x == z+x => y == z -}
           injR {- v++u == w++u => v == w -}
           unambigA {- showA u == showA v => u == v -}
           plusInjR {- x+y == x+z => y == z -}
           injL {- u++v == u++w => v == w -}
           inj1 {- v++(x:[]) == w++(x:[]) => v == w -}


       real    1m41.581s
       user    3m1.933s
       sys     0m3.747s
\end{verbatim}
}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Some other (simple!) grammars}

> Balanced nonparentheses: quad    Palindromes:
> B  ::=  A A                      P  ::=  a P a
> A  ::=  x A x                       |    b P b
>     |   y                           |    a
>                                     |    b
> Dyck language:                      |    epsilon
>
> D  ::=  ( D ) D
>    |    ( D )
>    |    ( )









\end{frame}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Post Correspondence Problem}

> | a1  | a2  | a3   | ...   | an  |
> | b1  | b2  | b3   | ...   | bn  |

\vp

> S  ::=  A | B
> A  ::=  x0  |  a1 A x1 |  a2 A x2   | ...   | an A xn
> B  ::=  x0  |  b1 B x1 |  b2 B x2   | ...   | bn B xn
> showS (A a)  = showA a
> showS (B b)  = showB b
>
> showA (A1 a)  = a1 ++ showA a ++ [X1]
> ...
> showA (An a)  = an ++ showA a ++ [Xn]
> ...
> showB (Bn b)  = bn ++ showB b ++ [Xn]

\vspace{2\baselineskip}

\end{frame}

\begin{frame}[fragile]{Post Correspondence Problem}

> | a1  | a2  | a3   | ...   | an  |
> | b1  | b2  | b3   | ...   | bn  |

> data X = X1 | X2 | ... | Xn
> upper  :: X -> [Tok]
> lower  :: X -> [Tok]
>
> forall  (xs :: [X]) zo'u   concatMap upper xs /= concatMap lower xs || null xs

> concatMap :: (a -> [b]) -> [a] -> [b]

\vspace{4\baselineskip}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Conclusions}

\begin{itemize}
\item Interesting class of problems
\item Very simple programs, very difficult proofs
\item How can we synthesise those functions for lemmas?
\end{itemize}

\end{frame}




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{}


\end{frame}




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{}


\end{frame}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{}


\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\begin{frame}[fragile]{}
%
%
%\end{frame}
%
%
%
%\begin{frame}{}
%
%
%\pause
%
%
%\pause
%
%\begin{center}
%$\{ a^nb^ma^{n'}b^{m'} | m = m' \vee n = n' \}$
%\end{center}
%
%\pause
%
%\begin{center}
%$\{ a^nb^mc^l | n = m \vee m = l \}$
%\end{center}
%
%\pause
%
%\(a^nb^nc^n\) is both \(n=m\) and \(m=l\).
%
%\end{frame}
%
%\begin{frame}{Inherent Ambiguity by Parikh}
%
%
%\pause
%
%
%\end{frame}
%
%\begin{frame}{}
%
%
%\pause
%
%
%\pause
%
%
%\end{frame}
%
%\begin{frame}{Generating function example}
%
%\begin{center}
%% $A \rightarrow \verb~"("~ \; A \; \verb~")"~ \; A \; | \; \epsilon$
%
%\pause
%
%$a(z) = z^2 a(z)^2 + 1$
%
%\pause
%
%$a(z) = 1 - \frac{\sqrt{1-4z^2}}{2z^2}$
%\pause
%
%
%\end{center}
%
%\end{frame}
%
%\begin{frame}[fragile]{Generating function example}
%
%
%\pause
%
%\begin{verbatim}
%     ()  ()()   (()())
%         (())   ()(())
%                (())()
%                ((()))
%                ()()()
%\end{verbatim}
%
%\end{frame}
%
%\begin{frame}{Chomsky-Schützenberger Theorem}
%
%The counting generating function of a context-free language with an
%unambiguous grammar is algebraic over \(\mathbb{Q}\).
%
%Contrapositively:
%
%If the counting generating function is transcendental over
%\(\mathbb{Q}\), then the language is inherently ambiguous.
%
%\end{frame}
%
%\begin{frame}{Goldstine language}
%
%\begin{center}
%$G =\{s^{n_1}z \; s^{n_2}z \; \cdots \; s^{n_p}z \mid p \geq 1, \exists i . n_i \neq i \}$
%\end{center}
%
%\pause
%
%
%\end{frame}
%
%\begin{frame}{More from \emph{Analytic Models and Ambiguity of CFLs}}
%
%All inherently ambiguous:
%
%\(O_3 = \{ w \in \{a,b,c\}^* \mid |w|_a = |w|_b \vee |w|_b = |w|_c \}\)
%
%\(O_4 = \{ w \in \{a,b,p,q\}^* \mid |w|_a = |w|_b \vee |w|_p = |w|_q \}\)
%
%\(\Omega_3 = \{ w \in \{a,b,c\}^* \mid |w|_a \neq |w|_b \vee |w|_b \neq |w|_c \}\)
%
%\(C = \{ w_1w_2 \mid w_1, w_2 \in \{a,b\}^*, w_1 = rev(w_1), w_2 = rev(w_2) \}\)
%
%\(S =\{s^{n}z \; w_1 \; s^{n}z \; w_2 \mid w_1, w_2 \in \{s,z\}*, n \geq 1 \}\)
%
%\ldots{}
%
%\end{frame}
%
%\begin{frame}{Unambiguity}
%
%Given pairs of \textbf{words}
%\(\{(a_1,b_1), (a_2, b_2), \ldots, (a_n,b_n)\}\), construct:
%
%\(A \rightarrow a_1 A x_1 \mid a_2 A x_2 \mid \cdots \mid a_n A x_n \mid x_0\)
%
%\(B \rightarrow b_1 B x_1 \mid b_2 B x_2 \mid \cdots \mid b_n B x_n \mid x_0\)
%
%\(S \rightarrow A \mid B\)
%
%(using fresh terminals \(x_0, \ldots, x_n\))
%
%\end{frame}
%
%\begin{frame}{Ambiguity Detection Methods, ADMs}
%
%\begin{itemize}
%\item
%  Exhaustive: sentence generation
%
%  \begin{itemize}
%  \item
%    AMBER
%  \item
%    CFG Analyzer
%  \end{itemize}
%\item
%  LR(k)
%\item
%  Approximative: false positives
%
%  \begin{itemize}
%  \item
%    ACLA, Ambiguity Checking with Language Approximations
%  \item
%    Noncanonical Unambiguity test
%  \end{itemize}
%\end{itemize}
%
%\end{frame}
%
%\begin{frame}{Exhaustive ADMs}
%
%\begin{centering}
%
%\end{centering}
%
%\end{frame}
%
%\begin{frame}{CFG Analyzer}
%
%
%\end{frame}
%
%\begin{frame}{CFG Analyzer, variables and encoding of derivability}
%
%
%
%
%
%
%\pause
%
%
%\end{frame}
%
%\begin{frame}{CFG Analyzer, encoding of ambiguity}
%
%\(E\): ambiguously nullable nonterminals
%(\(A \rightarrow \epsilon \mid \epsilon\)),
%
%\(M\): ambiguous nonterminals (\(A \rightarrow A\))
%
%
%\end{frame}
%
%\begin{frame}{CFG Analyzer, results}
%
%
%\end{frame}
%
%\begin{frame}{\texttt{ACLA}: Ambiguity Checking with Language
%Approximations}
%
%
%Conference on Implementation and Application of Automata 2007
%
%\end{frame}
%
%\begin{frame}{\textbf{Vertical} and horizontal ambiguity}
%
%With \(E\) being the set of terminals and nonterminals:
%
%
%\pause
%
%\(Z \rightarrow A \verb~y~\)
%
%\(Z \rightarrow \verb~x~ B\)
%
%\(A \rightarrow \verb~x~ \verb~a~\)
%
%\(B \rightarrow \verb~a~ \verb~y~\)
%
%\(xay \in L(A\verb~y~) \cap L(xB)\)
%
%\end{frame}
%
%\begin{frame}{Vertical and \textbf{horizontal} ambiguity}
%
%
%\pause
%
%\(Z \rightarrow \verb~x~ A B\)
%
%\(A \rightarrow \verb~a~\)
%
%\(A \rightarrow \epsilon\)
%
%\(B \rightarrow \verb~a~ \verb~y~\)
%
%\(B \rightarrow \verb~y~\)
%
%\(\verb~xay~ \in L(\verb~x~A) \cap\!\!\!\!\!^\vee L(B)\)
%
%\end{frame}
%
%\begin{frame}{Vertical and horizontal ambiguity}
%
%\begin{center}
%\end{center}
%
%\pause
%
%Grammar approximation:
%
%
%(\(\Sigma\) is the set of terminals, \(E\) terminals and non-terminals)
%
%\pause
%
%\pause
%
%
%Several approximations can be combined:
%
%
%\end{frame}
%
%\begin{frame}{Mohri and Nederhof negular approximation}
%
%\(P \rightarrow \verb~a~ \; P \; \verb~a~\)
%
%\(P \rightarrow \verb~b~ \; P \; \verb~b~\)
%
%\(P \rightarrow \verb~a~\)
%
%\(P \rightarrow \verb~b~\)
%
%\(P \rightarrow \epsilon\)
%
%\pause
%
%\(MN(\verb~a~ \; P \; \verb~a~) = \verb~a~ (\verb~a~ + \verb~b~) \verb~a~\)
%
%\(MN(\verb~b~ \; P \; \verb~b~) = \verb~b~ (\verb~a~ + \verb~b~) \verb~b~\)
%
%Disjoint: no vertical ambiguity
%
%\end{frame}
%
%\begin{frame}{Balancing parentheses}
%
%
%\pause
%
%
%\pause
%
%
%\end{frame}
%
%\begin{frame}{A balancing act\ldots{}}
%
%\(S \rightarrow A \; A\)
%
%\(A \rightarrow \verb~x~ \; A \; \verb~x~\)
%
%\(A \rightarrow \verb~y~\)
%
%\end{frame}
%
%\begin{frame}{Other approximations}
%
%
%\begin{itemize}
%\item
%  Empty string
%
%  \(E(\epsilon) = \Sigma^0\)
%
%  \(E(x) = \Sigma^{+}, x \neq \epsilon\)
%\item
%\item
%  First and last symbol
%\end{itemize}
%
%\end{frame}
%
%\begin{frame}{Evaluation on bioinformatics}
%
%
%\end{frame}
%
%\begin{frame}{Evaluation on Schmitz}
%
%
%\end{frame}
%
%\begin{frame}{}
%
%
%
%\end{frame}
%
%\begin{frame}{}
%
%
%
%\end{frame}

\end{document}
