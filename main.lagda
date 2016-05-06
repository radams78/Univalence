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

\DeclareUnicodeCharacter{8608}{\ensuremath{\twoheadrightarrow}}
\DeclareUnicodeCharacter{8667}{\ensuremath{\Rrightarrow}}
\DeclareUnicodeCharacter{8718}{\ensuremath{\qed}}
\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{9001}{\ensuremath{\langle}}
\DeclareUnicodeCharacter{9002}{\ensuremath{\rangle}}
\DeclareUnicodeCharacter{9655}{\ensuremath{\rhd}}
\DeclareUnicodeCharacter{10214}{\ensuremath{[}}
\DeclareUnicodeCharacter{10215}{\ensuremath{]}}
\DeclareUnicodeCharacter{10219}{\ensuremath{\rangle\rangle}}


\usepackage{textalpha}

\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}

\newtheorem{lemma}{Lemma}[section]
\theoremstyle{definition}
\newtheorem{definition}[lemma]{Definition}

\newcommand{\Set}{\mathbf{Set}}
\newcommand{\eqdef}{\mathrel{\smash{\stackrel{\text{def}}{=}}}}
\newcommand{\AgdaHide}[1]{}

\begin{document}

\maketitle

\input{Prelims.lagda}
\input{Grammar/Taxonomy.lagda}
\input{Grammar/Base.lagda}

We define the operations of replacement and substitution on
expressions.  The details are given in Appendix \ref{appendix:repsub}.

\input{Grammar/Context.lagda}
\input{Reduction.lagda}
\input{Reduction/SN.lagda}
\input{PL.lagda}
\input{PHOPL.lagda}

\appendix

\section{Replacement and Substitution}
\label{appendix:repsub}

\input{Grammar/OpFamily/PreOpFamily.lagda}
\input{Grammar/OpFamily/Lifting.lagda}
\input{Grammar/OpFamily/LiftFamily.lagda}
\input{Grammar/OpFamily/Composition.lagda}
\input{Grammar/OpFamily/OpFamily.lagda}
\input{Grammar/Replacement.lagda}
\input{Grammar/Substitution/PreOpFamily.lagda}
\input{Grammar/Substitution/Lifting.lagda}
\input{Grammar/Substitution/RepSub.lagda}
\input{Grammar/Substitution/LiftFamily.lagda}
\input{Grammar/Substitution/OpFamily.lagda}
\input{Grammar/Substitution/Botsub.lagda}

\end{document}
