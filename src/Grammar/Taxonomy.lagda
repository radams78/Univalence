\newcommand{\id}[1]{\mathsf{id}_{#1}}

\section{Grammars}

\subsection{Taxonomy}

\AgdaHide{
\begin{code}
module Grammar.Taxonomy where
open import Data.List public
open import Prelims
\end{code}
}

Before we begin investigating the several theories we wish to consider, we present a general theory of syntax and
capture-avoiding substitution.

A \emph{taxononmy} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, called the \emph{variable kinds}.  We refer to the other expession kinds as \emph{non-variable kinds}.
\end{itemize}

%<*Taxonomy>
\begin{code}
record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpressionKind : Set where
    varKind : VarKind → ExpressionKind
    nonVarKind : NonVarKind → ExpressionKind

  AbstractionKind : Set
  AbstractionKind = PiExp VarKind ExpressionKind
--TODO: Maybe get rid of NonVarKind?
\end{code}
%</Taxonomy>

A constructor $c$ of kind (\ref{eq:conkind}) is a constructor that takes $m$ arguments of kind $B_1$, \ldots, $B_m$, and binds $r_i$ variables in its $i$th argument of kind $A_{ij}$,
producing an expression of kind $C$.  We write this expression as

\begin{equation}
\label{eq:expression}
c([x_{11}, \ldots, x_{1r_1}]E_1, \ldots, [x_{m1}, \ldots, x_{mr_m}]E_m) \enspace .
\end{equation}

The subexpressions of the form $[x_{i1}, \ldots, x_{ir_i}]E_i$ shall be called \emph{abstractions}.

When giving a specific grammar, we shall feel free to use BNF notation.  

We formalise this as follows.  First, we construct the sets of expression kinds and constructor kinds over a taxonomy:

\begin{frame}[fragile]
There are two \emph{classes} of kinds: expression kinds and constructor kinds.

\begin{code}
  data KindClass : Set where
    -Expression : KindClass
    -Constructor : KindClass

  Kind : KindClass → Set
  Kind -Expression = ExpressionKind
  Kind -Constructor = List AbstractionKind
\end{code}
\end{frame}
%TODO Colours in Agda code?
