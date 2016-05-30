\newcommand{\id}[1]{\mathsf{id}_{#1}}

\section{Grammars}

\subsection{Taxonomy}

\AgdaHide{
\begin{code}
module Grammar.Taxonomy where
open import Data.List
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

\begin{frame}[fragile]
\frametitle{Grammars}
Example: Simply-typed lambda calculus
\[ \begin{array}{lrcl}
\text{Type} & A & ::= & \bot \mid A \rightarrow A \\
\text{Term} & M & ::= & x \mid \lambda x:A.M \mid M M
\end{array} \]

\begin{itemize}
\item
Two kinds: `Type' (non-variable kind) and `Term' (variable kind)
\item
Four constructors:
\begin{itemize}
\item
$\bot$ --- kind Type
\item
$\rightarrow$ --- kind (Type, Type) Type
\item
$\lambda$ --- kind (Type, (Term) Term) Term
\item
$app$ --- kind (Term, Term) Term
\end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Grammars}
A \emph{grammar} consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, called the \emph{variable kinds}.  We refer to the other expession kinds as \emph{non-variable kinds}.
\item a set of \emph{constructors}, each with an associated \emph{constructor kind} of the form
\begin{equation}
\label{eq:conkind}
 ((A_{11}, \ldots, A_{1r_1}) B_1, \ldots, (A_{m1}, \ldots, A_{mr_m}) B_m) C
\end{equation}
where each $A_{ij}$ is a variable kind, and each $B_i$ and $C$ is an expression kind.
\item a function assigning, to each variable kind $K$, an expression kind, the \emph{parent} of $K$.
\end{itemize}
\end{frame}

\begin{frame}[fragile]
A \emph{taxonomy } consists of:
\begin{itemize}
\item a set of \emph{expression kinds};
\item a subset of expression kinds, called the \emph{variable kinds}.  We refer to the other expession kinds as \emph{non-variable kinds}.
\end{itemize}

\begin{code}
record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpressionKind : Set where
    varKind : VarKind → ExpressionKind
    nonVarKind : NonVarKind → ExpressionKind
\end{code}
\end{frame}

\begin{frame}[fragile]
\frametitle{Alphabets}
An \emph{alphabet} $A$ consists of a finite set of \emph{variables},
\mode<article>{to each of which is assigned a variable kind $K$.
Let $\emptyset$ be the empty alphabet, and $(A , K)$ be the result of extending the alphabet $A$ with one
fresh variable $x₀$ of kind $K$.  We write $\mathsf{Var}\ A\ K$ for the set of all variables in $A$ of kind $K$.}
\mode<beamer>{each with a variable kind.}

\begin{code}
  infixl 55 _,_
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet
\end{code}

\AgdaHide{
\begin{code}
  extend : Alphabet → List VarKind → Alphabet
  extend A [] = A
  extend A (K ∷ KK) = extend (A , K) KK

  snoc-extend : Alphabet → snocList VarKind → Alphabet
  snoc-extend A [] = A
  snoc-extend A (KK snoc K) = snoc-extend A KK , K
\end{code}
}

\begin{code}
  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L
\end{code}

\AgdaHide{
\begin{code}
  x₁ : ∀ {V} {K} {L} → Var (V , K , L) K
\end{code}
}

\begin{code}
  x₁ = ↑ x₀
\end{code}

\AgdaHide{
\begin{code}
  x₂ : ∀ {V} {K} {L} {L'} → Var (V , K , L , L') K
\end{code}
}

\begin{code}
  x₂ = ↑ x₁
\end{code}
\end{frame}

\mode<article>{
A \emph{grammar} over a taxonomy consists of:
\begin{itemize}
\item a set of \emph{constructors}, each with an associated \emph{constructor kind} of the form
\begin{equation}
\label{eq:conkind}
 ((A_{11}, \ldots, A_{1r_1}) B_1, \ldots, (A_{m1}, \ldots, A_{mr_m}) B_m) C
\end{equation}
where each $A_{ij}$ is a variable kind, and each $B_i$ and $C$ is an expression kind.
\item a function assigning, to each variable kind $K$, an expression kind, the \emph{parent} of $K$.
\end{itemize}

A constructor $c$ of kind (\ref{eq:conkind}) is a constructor that takes $m$ arguments of kind $B_1$, \ldots, $B_m$, and binds $r_i$ variables in its $i$th argument of kind $A_{ij}$,
producing an expression of kind $C$.  We write this expression as

\begin{equation}
\label{eq:expression}
c([x_{11}, \ldots, x_{1r_1}]E_1, \ldots, [x_{m1}, \ldots, x_{mr_m}]E_m) \enspace .
\end{equation}

The subexpressions of the form $[x_{i1}, \ldots, x_{ir_i}]E_i$ shall be called \emph{abstractions}.

When giving a specific grammar, we shall feel free to use BNF notation.  

We formalise this as follows.  First, we construct the sets of expression kinds and constructor kinds over a taxonomy:
}

\begin{frame}[fragile]
There are two \emph{classes} of kinds: expression kinds and constructor kinds.

\begin{code}
  data KindClass : Set where
    -Expression : KindClass
    -Constructor : ExpressionKind → KindClass

  data AbstractionKind : Set where
    _⟶_ : List VarKind → ExpressionKind → AbstractionKind

  data Kind : KindClass → Set
  ConstructorKind : ExpressionKind → Set

  ConstructorKind K = Kind (-Constructor K)

  data Kind where
    base : ExpressionKind → Kind -Expression

    out  : ∀ K → Kind (-Constructor K)
    _⟶_ : ∀ {K} → AbstractionKind → Kind (-Constructor K) → Kind (-Constructor K)

  Π    : ∀ {K} → List VarKind → ExpressionKind → 
         Kind (-Constructor K) → Kind (-Constructor K)
  Π A K L = (A ⟶ K) ⟶ L
--TODO Inline
 \end{code}
\end{frame}
%TODO Colours in Agda code?
