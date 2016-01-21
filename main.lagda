\documentclass{article}

\title{Type Theories with Computation Rules for the Univalence Axiom}
\author{Robin Adams}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{fancyvrb}
\usepackage{proof}
\usepackage{stmaryrd}

\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{9001}{\ensuremath{\langle}}
\DeclareUnicodeCharacter{9002}{\ensuremath{\rangle}}
\DeclareUnicodeCharacter{9655}{\ensuremath{\rhd}}
\DeclareUnicodeCharacter{10219}{\ensuremath{\rangle\rangle}}

\renewcommand{\textbeta}{\ensuremath{\beta}}
\renewcommand{\textgamma}{\ensuremath{\gamma}}
\renewcommand{\textGamma}{\ensuremath{\Gamma}}
\renewcommand{\textdelta}{\ensuremath{\delta}}
\renewcommand{\textDelta}{\ensuremath{\Delta}}
\renewcommand{\textepsilon}{\ensuremath{\epsilon}}
\renewcommand{\textLambda}{\ensuremath{\Lambda}}
\renewcommand{\textlambda}{\ensuremath{\lambda}}
\renewcommand{\textphi}{\ensuremath{\phi}}
\renewcommand{\textpsi}{\ensuremath{\psi}}
\renewcommand{\textsigma}{\ensuremath{\sigma}}
\renewcommand{\textrho}{\ensuremath{\rho}}
\renewcommand{\textOmega}{\ensuremath{\Omega}}
\renewcommand{\texttau}{\ensuremath{\tau}}
\renewcommand{\textxi}{\ensuremath{\xi}}

\DefineVerbatimEnvironment{code}{Verbatim}{}

\newtheorem{lemma}{Lemma}

\newcommand{\Set}{\mathbf{Set}}

\begin{document}

\maketitle

\begin{code}
module main where
\end{code}

\input{Prelims.lagda}
\begin{code}
open import Prelims
\end{code}

\input{PL.lagda}

\input{PHOPL.lagda}

\end{document}
